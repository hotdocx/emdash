# TypeScript/emdash Affine Algebraic Geometry Plan

Date: 2026-08-30

Plan-ID: `TS-EMDASH-AFFINE-ALGEBRAIC-GEOMETRY`

Status: living architecture and implementation ledger; dedicated branch and
worktree created; `AFFINE-QUOTIENT-1A` is complete and proportional-green;
`AFFINE-MAPS-1B` is complete and proportional-green; `AFFINE-LOCALIZATION-2A`
is the next dependency-ready row.

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
| `AFFINE-QUOTIENT-1A` | complete; proportional-green at `9b0a1e0` | CAS ideals, reduced Gröbner bases, membership | reduced-basis structural parents, whole reductions, canonical elements, arithmetic/equality, schemas/serialization, native operations, graphs, edge cases, cancellation, and real Singular smoke comparison complete |
| `AFFINE-MAPS-1B` | complete; proportional-green at `9ef4027` | `AFFINE-QUOTIENT-1A` | presented algebra wrappers, relation-checked generator-image maps, polynomial/element evaluation, identity/composition/equality, schemas, native application, graphs, and invalid-map diagnostics complete |
| `AFFINE-LOCALIZATION-2A` | pending; next selected row | `AFFINE-MAPS-1B` | principal localization by adjoining an inverse, canonical map/inverse data, and basic-open coordinate charts |
| `AFFINE-SCHEMES-2B` | pending | `AFFINE-LOCALIZATION-2A` | affine schemes, contravariant morphisms, closed immersions, basic-open immersions, and a strict computational category |
| `AFFINE-TENSOR-3A` | pending | `AFFINE-MAPS-1B`, `AFFINE-SCHEMES-2B` | presented tensor products, universal maps, compatibility computations, and affine fiber products |
| `AFFINE-COVERS-4A` | pending | `AFFINE-LOCALIZATION-2A`, existing unimodular covers | actual finite affine charts, overlaps, restriction maps, Cech nerve, and initial cochain data |
| `AFFINE-GRAPH-5A` | pending | one representative consumer from each preceding layer | native operation bundles, computation graphs, affine category/tower metadata, direct reinterpretations, and staged compilation |
| `AFFINE-SINGULAR-6A` | pending | installed Singular and representative native consumers | real opt-in differential comparisons for radical, quotient, localization, and selected fiber-product computations |
| `AFFINE-FORMAL-CONSUMER-7` | deferred | completed finite-cover/Cech consumer and separate user authorization | inspect the concrete consumer and launch or specify the minimal follow-up formal-bridge goal; not an affine computation prerequisite |

Rows may be split into lettered subtranches when needed. A row is complete only
after implementation, focused positive and negative tests, proportional
validation, synchronized decisions/results, and a local checkpoint.

## Decision Ledger

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-AFFINE-001` | accepted | Quotient-parent identity is owned by the fixed polynomial ring and canonical reduced Gröbner basis, so scaled or otherwise equivalent generator presentations share one structural quotient identity. |
| `D-AFFINE-002` | accepted | A quotient element stores only its reduced Gröbner remainder; the whole reduction separately retains the input polynomial, basis quotients, original-generator coefficients, and remainder. |
| `D-AFFINE-003` | accepted | Quotient arithmetic always renormalizes after polynomial arithmetic, and equality is structural-parent agreement plus canonical polynomial equality. |
| `D-AFFINE-004` | accepted | The quotient layer exposes direct commutative-ring operations rather than pretending to implement the existing ordered-domain interface; a quotient ring has no canonical total order. |
| `D-AFFINE-005` | accepted | Zero and unit ideals use the same representation and algorithms as every other quotient; in the unit quotient, zero and one compute equal without a special zero-ring branch. |
| `D-AFFINE-006` | accepted | Singular is installed and the existing real radical-membership adapter was exercised successfully against it; external agreement remains focused non-authoritative evidence. |
| `D-AFFINE-007` | accepted | A presented algebra is the canonical quotient owner from `AFFINE-QUOTIENT-1A`; the wrapper supplies algebraic role and variance without duplicating quotient normalization. |
| `D-AFFINE-008` | accepted | A map is determined by one target quotient element for every ordered source polynomial generator, and construction evaluates every source ideal generator and requires canonical zero. |
| `D-AFFINE-009` | accepted | Polynomial and quotient-element application uses exact substitution into target quotient arithmetic; identity uses source variables, composition substitutes the first map's generator images through the second, and equality compares canonical generator images. |
| `D-AFFINE-010` | accepted | The first native map operation fixes one already-validated map and applies it to source quotient elements, preserving source/target schemas without serializing callbacks or decompiling TypeScript. |

## `AFFINE-MAPS-1B` Result

Finitely presented algebras and relation-checked maps are implemented in
`src/v3_2/algebra_presented_algebra.ts`. A map retains source and target
algebras, canonical target images for every ordered source generator, and the
computed image of every source relation. Construction fails if any relation
does not normalize to zero.

Exact substitution applies maps to source polynomials and quotient elements.
Identity, composition, and equality are defined entirely through canonical
generator images. A stable map schema reconstructs and revalidates those
images and relations. The native operation in
`src/v3_2/algebra_presented_algebra_reference_operations.ts` applies one fixed
validated map through the ordinary graph engine.

Seven focused map tests cover valid and invalid relation images, generator
arity, quotient-element application, identity, composition, canonical map
equality, schemas, foreign elements, noncomposable maps, and retained graph
execution. Together with affected quotient, graph, and reference-engine
suites, 36 tests pass, followed by workspace check, affected lint, root
typecheck, and diff hygiene. `check:ts` was not run.

Semantic checkpoint: `9ef4027` (`affine: add relation-checked algebra maps`).

## `AFFINE-QUOTIENT-1A` Result

Canonical polynomial quotient rings are implemented in
`src/v3_2/algebra_quotient.ts`. A parent retains its polynomial ring, source
ideal, and reduced Gröbner basis; an exact safe fingerprint of that canonical
basis enters the parent identity. A whole reduction reuses ideal membership to
retain original-generator coefficients, basis quotients, and the remainder.
Elements store only that remainder.

The layer supplies zero, one, addition, negation, multiplication, nonnegative
powers, equality, text, serialization, and schemas. The ring-specific native
bundle in `src/v3_2/algebra_quotient_reference_operations.ts` exposes whole
reduction, normalization, negation, addition, multiplication, and powers.
Retained graphs normalize/double-negate representatives and multiply external
quotient pairs.

Eight quotient tests cover equivalent representatives, nilpotence in
`Q[x]/(x^2)`, canonical identity across scaled relations, zero and unit ideals,
schemas, serialization, foreign polynomial/quotient parents, negative powers,
graph execution, and cancelled Gröbner construction. Together with affected
ideal, graph, and reference-engine suites, 40 tests pass, followed by workspace
check, affected lint, root typecheck, and diff hygiene. `check:ts` was not run.

The installed Singular executable also returned agreement with the native
Rabinowitsch radical-membership decision for `x in sqrt((x^2))`.

Semantic checkpoint: `9b0a1e0` (`affine: add canonical quotient rings`).

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
