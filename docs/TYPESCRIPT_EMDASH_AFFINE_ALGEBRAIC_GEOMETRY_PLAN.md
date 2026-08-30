# TypeScript/emdash Affine Algebraic Geometry Plan

Date: 2026-08-30

Plan-ID: `TS-EMDASH-AFFINE-ALGEBRAIC-GEOMETRY`

Status: living architecture and implementation ledger; dedicated branch and
worktree created; quotient rings are the first dependency-ready row.

Baseline: `1095fab1fd64de6a2793f6958721bedc4b550f21`

Branch: `goal/affine-algebraic-geometry-cas-v3.2`

Worktree: `/home/user1/emdash1-affine-cas-v1`

## Purpose

This plan governs the first concrete affine-algebraic-geometry layer over the
completed focused TypeScript CAS and staged computable-categorical engine.
The implementation path is:

```text
quotient rings and presented algebras
        -> algebra maps
        -> principal localizations
        -> affine schemes and morphisms
        -> closed and basic-open subschemes
        -> tensor products and affine fiber products
        -> finite affine covers and Cech nerves
```

The goal is executable affine geometry, not a speculative proof adapter.
Computations remain useful in their own right and retain the whole data needed
by later formal or categorical consumers.

## Relationship To The Focused CAS And Formal Bridge

The authoritative computational substrate is the completed plan
`docs/TYPESCRIPT_EMDASH_FOCUSED_CAS_AND_CATEGORICAL_ENGINE_PLAN.md` at the
baseline above. This goal consumes, but does not redesign without evidence:

- exact coefficient domains and sparse polynomial rings;
- ideals, Gröbner bases, membership, elimination, saturation, and radicals;
- polynomial modules and Schreyer resolutions;
- constructible sets and the staged category/tower compiler;
- `AlgebraOperation`, `AlgebraComputationGraph`, and the native reference
  engine; and
- the opt-in Singular differential-oracle boundary.

The affine implementation is not a logical prerequisite for
`CAS-FORMAL-BRIDGE-10`. Rather, it is the recommended concrete consumer that
will determine what that bridge actually needs to transport. Once finite
basic-open charts, overlaps, and Cech data exist, a follow-up goal may select
the minimal explicit-data, trusted-computation, or checked-witness adapter.
This goal does not implement a formal bridge merely because one is possible.

## Governing Principles

1. Quotient and localization equality is computational normal-form equality,
   never unreduced presentation syntax.
2. Whole constructions retain their input presentations, Gröbner data,
   canonical maps, and comparison paths or decompositions where useful.
3. Ring maps are validated by sending every source relation to zero in the
   target; identity and composition remain explicit.
4. Affine morphisms are contravariant algebra maps. Variance is represented in
   the API rather than hidden in naming conventions.
5. Principal localization is implemented as adjoining an inverse,
   `R[t]/(t f - 1)`, so it reuses quotient-ring and Gröbner machinery.
6. Fiber products use presented tensor products and retain the universal maps.
7. Finite covers retain actual chart localizations, overlaps, refinement maps,
   and Cech indexing data—not only a unimodularity Boolean.
8. Native execution remains the default. Singular is a differential oracle,
   never a semantic owner or production prerequisite.
9. Formal adoption is consumer-gated and does not block computation.
10. Validation is proportional. `check:ts` and repository-wide aggregates are
    explicitly deferred unless the user later requests an integration gate.

## Target Architecture

```text
surface affine programs / direct TypeScript construction
                         |
                         v
presented algebras, maps, affine schemes, covers, Cech data
                         |
                         v
staged categorical programs and affine constructor metadata
                         |
                         v
AlgebraComputationGraph
                         |
             +-----------+-----------+
             |                       |
             v                       v
native TypeScript engine      opt-in Singular oracle
```

These contributor APIs remain under `src/v3_2` until a separate graduation
decision. They are not added to distributable package barrels in this goal.

## Mathematical And Computational Design

### Quotient rings

For a polynomial ring `R` over an operational field and ideal `I`, a quotient
parent `R/I` retains a reduced Gröbner basis of `I`. Every quotient element is
stored as the canonical remainder of one polynomial. Construction, addition,
negation, multiplication, powers, equality, text/serialization, schemas, and
graph operations all normalize through that owner.

The whole reduction result retains the input polynomial, basis quotients,
original-generator coefficients, and remainder when a consumer needs the
computation path. Quotient-ring elements never use JavaScript `number` for
exact coefficients.

### Presented commutative algebras and maps

A finitely presented algebra over a base coefficient field is a quotient of a
sparse polynomial ring. A map is specified by the images of source generators.
Construction substitutes those images into every source relation and requires
zero in the target quotient. Maps retain source, target, generator images, and
relation checks. Identity, composition, element application, and equality are
computational.

The first implementation is parent-polymorphic over the existing operational
field interface. Curated examples begin over `Q`; this is test selection, not
an architectural hard-code.

### Principal localization and basic opens

For `f in A`, construct

```text
A_f = A[t] / (t f - 1).
```

Retain the extended presentation, canonical map `A -> A_f`, the distinguished
inverse of `f`, and the equation computation. A basic-open chart `D(f)` uses
that localization as its coordinate algebra. Products `f_1 ... f_n` model
higher intersections without a separate fraction syntax.

### Affine schemes and morphisms

`Spec(A)` retains its presented coordinate algebra. A morphism
`Spec(B) -> Spec(A)` retains the contravariant algebra map `A -> B`. Closed
immersions arise from quotient maps; basic-open immersions arise from
localization maps. Runtime identities and composition follow algebra-map
identity and reverse composition.

This ordinary strict/set-level computational category does not impose its
equality on emdash's full omega-categorical semantics.

### Tensor products and affine fiber products

Given compatible presented algebra maps `A -> B` and `A -> C`, construct a
presentation of `B tensor_A C` by combining generators and relations and
adding equations identifying both images of every selected generator of `A`.
Retain canonical maps from `B` and `C`, their compatibility computation, and
the universal application operation. The corresponding affine scheme is

```text
Spec(B) x_{Spec(A)} Spec(C) = Spec(B tensor_A C).
```

### Finite affine covers and Cech data

Convert an existing positive unimodular family into actual localized affine
charts. Retain pairwise and higher overlaps via product localizations, ordered
simplex indices, restriction algebra maps, and simplicial face data. The first
Cech layer owns the nerve and initial cochain-complex presentation; derived or
sheaf-cohomology claims require their own later rows.

### Native operations and staged categorical execution

Every high-value whole operation must have an `AlgebraOperation` contract and
be executable directly or through `AlgebraComputationGraph`. Add category
operations and constructor/lowering metadata only when a concrete affine
program consumes them. Reinterpret direct presented algebras and schemes as
the efficient public representation rather than building runtime wrapper
towers.

### Real Singular differential checks

Singular is installed locally. Early in this goal, run the existing
radical-membership adapter against the real executable and correct the script
or transport if necessary. Later comparisons cover quotient normal forms,
saturation, selected localization presentations, and fiber-product ideals.

External comparisons are opt-in focused evidence. They do not replace native
tests, define API semantics, or require `check:ts`.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `AFFINE-PLAN-0` | complete | completed focused-CAS goal and reviewed continuation | this living plan, isolated branch/worktree, architecture, staged rows, validation policy, and Git limits |
| `AFFINE-QUOTIENT-1A` | pending; next selected row | CAS ideals, reduced Gröbner bases, membership | quotient-ring parents and canonical elements; arithmetic, equality, schemas, serialization, retained reduction, native operations, and graph execution |
| `AFFINE-MAPS-1B` | pending | `AFFINE-QUOTIENT-1A` | presented algebras and relation-checked algebra maps with identity, composition, application, and equality |
| `AFFINE-LOCALIZATION-2A` | pending | `AFFINE-MAPS-1B` | principal localization by adjoining an inverse, canonical map/inverse data, and basic-open coordinate charts |
| `AFFINE-SCHEMES-2B` | pending | `AFFINE-LOCALIZATION-2A` | affine schemes, contravariant morphisms, closed immersions, basic-open immersions, and a strict computational category |
| `AFFINE-TENSOR-3A` | pending | `AFFINE-MAPS-1B`, `AFFINE-SCHEMES-2B` | presented tensor products, universal maps, compatibility computations, and affine fiber products |
| `AFFINE-COVERS-4A` | pending | `AFFINE-LOCALIZATION-2A`, existing unimodular covers | actual finite affine charts, overlaps, restriction maps, Cech nerve, and initial cochain data |
| `AFFINE-GRAPH-5A` | pending | one representative consumer from each preceding layer | native operation bundles, computation graphs, affine category/tower metadata, direct reinterpretations, and staged compilation |
| `AFFINE-SINGULAR-6A` | pending | installed Singular and representative native consumers | real opt-in differential comparisons for radical, quotient, localization, and selected fiber-product computations |
| `AFFINE-FORMAL-CONSUMER-7` | deferred | completed finite-cover/Cech consumer and separate user authorization | inspect the concrete consumer and launch or specify the minimal follow-up formal-bridge goal; not an affine computation prerequisite |

Rows may be split into lettered subtranches when needed. A row is complete only
after implementation, focused positive and negative tests, proportional
validation, synchronized decisions/results, and a local checkpoint.

## Initial `AFFINE-QUOTIENT-1A` Tranche

The first bounded implementation owns:

- a structural quotient-ring parent over one polynomial ring and ideal;
- one retained reduced Gröbner basis as the canonical reduction owner;
- quotient elements storing only canonical remainders;
- a whole reduction result retaining membership coefficients and remainder;
- zero, one, arithmetic, powers, equality, text, and serialization;
- runtime schemas rejecting foreign quotient parents and inexact input;
- a ring-specific native reduction/arithmetic operation bundle;
- a graph that reduces and combines quotient elements; and
- focused tests including nilpotents, equivalent representatives, foreign
  parents, zero/unit ideals, and bounded/cancelled Gröbner work.

It does not yet own arbitrary algebra maps, localizations, schemes, tensor
products, Cech data, or formal adapters.

## Validation Policy

Use proportional validation only:

- focused new tests plus directly affected polynomial/ideal/engine suites;
- `./scripts/pnpmw run workspace:check` at bounded checkpoints;
- root typecheck;
- affected-file ESLint;
- `git diff --check` and exact staged-diff review;
- installed Singular comparisons only for the affected oracle cases; and
- no `check:ts`, `check:all`, kernel, print, book, package-release, or browser
  aggregate unless a later explicit integration request changes the boundary.

Wiring a focused test into `tests/main_tests.ts` does not itself justify the
aggregate test runner.

## Git Authorization And Checkpoints

The user authorizes local checkpoint commits on this dedicated branch as work
progresses. A checkpoint requires a bounded green tranche, synchronized living
plan, and exact staged diff containing no unrelated work.

This authorization does not include pushing, merging, rebasing, amending,
history rewriting, publishing, releasing, opening a PR, deleting branches, or
removing worktrees. Integration to `main` and any complete TypeScript gate are
separate future decisions.

## Completion Boundary

This goal is complete when every nondeferred affine ledger row is implemented,
validated, documented, and checkpointed; the native CAS remains the default;
real Singular checks are opt-in and non-authoritative; and the completed cover
consumer makes the follow-up formal-bridge requirements concrete. It is not
complete merely because quotient rings or one affine example works.
