# TypeScript/emdash Presented-Algebra Modules And Affine Descent Plan

Date: 2026-08-31

Plan-ID: `TS-EMDASH-PRESENTED-ALGEBRA-MODULES`

Status: living architecture and implementation ledger; dedicated branch and
worktree created from the completed affine-formal baseline;
`PAM-AUDIT-1A` is the next dependency-ready row.

Baseline: `c5f134b50ff8c169ba5d2f6abd12d82c04c97740`

Branch: `goal/presented-algebra-modules-v3.2`

Worktree: `/home/user1/emdash1-presented-algebra-modules-v1`

## Purpose

This plan governs the next concrete computational layer after the focused CAS,
affine geometry, and affine formal bridge: finitely presented modules over
finitely presented commutative algebras, their functorial base change and
localization, and the resulting module-valued affine Čech data.

The target path is:

```text
A = k[x]/I
      |
      v
finite free and presented A-modules
      |
      v
relation-checked linear and semilinear maps
      |
      v
B tensor_A M for A -> B
      |
      v
M[1/f] on basic-open charts
      |
      v
quasi-coherent affine-module presentation
      |
      v
ordered module-valued Cech diagram
      |
      v
native AlgebraOperation / graph / categorical lowering
```

This is computation-first algebraic geometry. It is not a proof-certificate
project, a general sheaf category, or a speculative formal adapter.

## Authority And Prerequisites

The completed computational authorities are:

- `docs/TYPESCRIPT_EMDASH_FOCUSED_CAS_AND_CATEGORICAL_ENGINE_PLAN.md`;
- `docs/TYPESCRIPT_EMDASH_AFFINE_ALGEBRAIC_GEOMETRY_PLAN.md`; and
- the active `src/v3_2/algebra_*` owners selected by those plans.

The completed optional formal boundary is recorded in
`docs/TYPESCRIPT_EMDASH_AFFINE_FORMAL_BRIDGE_PLAN.md`. This goal may retain
data useful to a later formal module consumer, but it does not extend the
formal bridge merely because the ring-level bridge now exists.

For TypeScript architecture and validation, follow the root `AGENTS.md`,
`docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`, and
`docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`. The old root category-specific
prototype remains non-authoritative. No Lambdapi source or active kernel owner
is expected in the initial implementation path.

The branch deliberately excludes the ongoing orthogonal
`goal/path-cubical-groupoidal-api-v3.2` history. Local `main` was
fast-forwarded only through the focused-CAS, affine-geometry, and
affine-formal line before this worktree was created.

## Governing Principles

1. Reuse the existing polynomial-module Gröbner and Schreyer engine. Do not
   build a second unrelated module normalizer for quotient algebras.
2. A module over `A = k[x]/I` is computed through one polynomial-module
   presentation containing both `I` acting on every free basis vector and the
   selected module relations.
3. Public module elements use canonical quotient-module normal forms. Raw
   polynomial vectors and reduction decompositions remain retained evidence,
   not equality.
4. Parent identity includes the presented algebra, free rank, module term
   order, and canonical relation-submodule owner. Incompatible parents fail
   closed.
5. Cross-ring module maps are explicit semilinear maps over one selected
   presented-algebra map. Ordinary linear maps are the identity-base-map
   specialization.
6. Map construction validates every source relation in the target module.
   Identity, composition, application, and equality use canonical module
   normal forms; no hand-entered commutative square is stored.
7. Base change `B tensor_A M` transports a whole presentation along
   `A -> B`, retaining the algebra map, original module, transported
   relations, result module, and canonical semilinear map.
8. Module localization is base change along the existing whole principal
   localization. It introduces no separate fraction syntax or localization
   parent.
9. An affine quasi-coherent presentation is an affine scheme plus a module
   over its coordinate algebra and derived chart/overlap base changes. It is
   presentation data, not a claim of a general sheaf theorem.
10. Čech restrictions derive from semilinear base change along the existing
    face algebra maps. Indices, products, removed positions, signs, and whole
    restriction computations remain available.
11. A varying-ring Čech module diagram is not silently collapsed to one
    ordinary chain complex. Restriction of scalars, a total category, a
    differential, `d² = 0`, or sheaf cohomology require their own concrete
    consumer and representation decision.
12. Native TypeScript remains the default engine. Singular or another CAS is
    an opt-in differential oracle, not a semantic owner.
13. Whole constructions are primary. CAP-style projections and convenient
    with-given facades may derive from retained whole values.
14. Validation is proportional. `check:ts`, `check:all`, kernel, book,
    browser, and package aggregates remain outside ordinary rows unless an
    actually affected shared boundary or later explicit request requires one.

## Core Representation Decision To Audit

For `A = R/I` and free rank `r`, the selected candidate is:

```text
A^r / N

represented computationally as

R^r / (I R^r + N_lift).
```

The `I R^r` generators are formed by multiplying every selected canonical
generator of `I` by every ordered free basis vector. User module relations are
accepted through `A`-valued components, lifted from their canonical quotient
representatives, and combined with the scalar-action relations. The existing
module Gröbner basis supplies normal forms, equality, and reconstruction.

`PAM-AUDIT-1A` must settle the exact choices before promotion:

- source ideal generators versus the canonical reduced Gröbner basis as the
  `I R^r` owner;
- public relation acquisition and retained original/canonical forms;
- POT/TOP default and parent identity;
- canonical element representation and zero-module detection;
- how module-presentation identities remain stable across equivalent algebra
  presentations; and
- the exact relation between the new owner and
  `AlgebraPresentedPolynomialModule`.

The audit may revise this representation if a focused counterexample rejects
it. It must not implement a weaker componentwise scalar-ideal approximation.

## Proposed Implementation Sequence

### 1. Owner and representation audit

Trace the current polynomial free-module, submodule, module Gröbner,
presented-polynomial-module, quotient-algebra, algebra-map, localization,
tensor, cover, and graph owners. Implement the smallest disposable prototype
needed to verify that `R^r/(IR^r+N)` gives canonical `A`-module normal forms
and survives the first localization example.

The audit acceptance examples are:

- `A = Q[x]/(x²)`, rank one, with no extra module relation;
- `A = Q[x]`, `M = A/(x)`; and
- two canonically equal quotient representatives producing identical module
  elements.

### 2. Presented modules over presented algebras

Implement parent-aware finite free and finitely presented `A`-modules,
canonical elements, whole normalization, zero/one-basis constructors,
addition, negation, scalar multiplication, equality, zero-module detection,
schemas, deterministic serialization, and negative diagnostics.

The whole normal-form result retains:

- the input `A`-valued vector;
- its canonical polynomial lift;
- combined algebra-action and module relations;
- the computed module Gröbner basis;
- basis quotients and original-relation coefficients; and
- the canonical remainder.

### 3. Linear and semilinear module maps

Implement one map representation over an explicit algebra map `phi : A -> B`.
It stores the image of every ordered source basis vector as a target-module
element and verifies all source relations after scalar transport. Provide:

- identity over `id_A`;
- composition over algebra-map composition;
- element application;
- canonical equality and zero testing; and
- the ordinary `A`-linear specialization.

No separate manually supplied naturality or relation square is accepted.

### 4. Functorial base change

For `phi : A -> B`, construct `B tensor_A M` by transporting the complete
module presentation into the target polynomial module and adding the target
algebra-action relations. Retain the canonical `phi`-semilinear map, relation
checks, transported generator order, and whole comparison data.

Base change must compute on module maps and satisfy focused computational
identity/composition comparisons. These comparisons are data and tests, not
new logical equality axioms.

### 5. Principal localization of modules

Specialize base change along the existing canonical map `A -> A[1/f]`.
Retain the whole ring localization and module base-change result. Required
examples include:

```text
A = Q[x], M = A/(x)

M[1/x]       = 0
M[1/(1-x)]   remains nonzero.
```

Units, nilpotents, canonical-equal denominators, foreign modules, and fresh
inverse-variable collisions remain ordinary focused cases.

### 6. Affine quasi-coherent module presentation

Package one affine scheme `Spec(A)` with one presented `A`-module `M`.
Construct its values on selected basic opens and product-overlap charts by
module localization. Preserve the ambient module, chart identity, algebra
localizations, and canonical semilinear maps.

This layer does not claim essential surjectivity of the affine module/sheaf
correspondence, sheafification, descent effectiveness, or a general category
of quasi-coherent sheaves.

### 7. Module-valued affine Čech diagram

Use the existing ordered affine cover simplices and face algebra maps.
Associate each simplex with the direct localization of `M` at its product and
each face with the induced semilinear restriction into the containing
product chart. Retain:

- simplex degree and increasing indices;
- product localization and localized module;
- removed position/chart and sign;
- algebra restriction map;
- relation-checked semilinear module map; and
- computational composition/identity comparisons for repeated faces.

The first row ends at this varying-ring diagram. A single differential or
cohomology object is explicitly deferred.

### 8. Native operations, graphs, and categorical compilation

Expose whole module normalization, semilinear map application, base change,
module localization, quasi-coherent chart realization, and Čech-module
construction through exact `AlgebraOperation` contracts. Add graph and
CAP-style categorical/tower lowerings only for representative consumers whose
schemas match without coercive wrappers.

### 9. Differential oracle and conformance examples

Use Singular module operations only where they offer a stable, deterministic
comparison for selected module Gröbner, normal-form, or localization cases.
Oracle absence or mismatch remains data and never blocks the native engine.

Conformance examples are:

- `A = Q[x]`, `M = A/(x)`, cover `D(x), D(1-x)`; and
- `A = Q[x,y]`, `M = A/(x,y)`, cover
  `D(x), D(y), D(1-x-y)` through degree two.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `PAM-PLAN-0` | complete | completed focused CAS, affine geometry, affine formal bridge, and reviewed continuation | this living plan, dedicated branch/worktree, exact baseline, architecture, staged rows, proportional validation, and Git limits |
| `PAM-AUDIT-1A` | pending; next selected row | current polynomial-module and affine owners | exact owner/consumer map, accepted or revised quotient-module representation, parent/equality decision, first localization prototype, and focused baseline evidence |
| `PAM-MODULE-2A` | pending | `PAM-AUDIT-1A` | parent-aware free/presented modules over presented algebras, canonical elements and whole normal forms, arithmetic, schemas, serialization, zero detection, and negative diagnostics |
| `PAM-SEMILINEAR-3A` | pending | `PAM-MODULE-2A`, presented-algebra maps | relation-checked semilinear maps, ordinary linear specialization, identity/composition/application/equality, and retained relation checks |
| `PAM-BASECHANGE-4A` | pending | `PAM-SEMILINEAR-3A` | whole module base change on objects and maps, canonical semilinear unit, identity/composition comparisons, schemas, and diagnostics |
| `PAM-LOCALIZATION-5A` | pending | `PAM-BASECHANGE-4A`, principal localizations | module localization as base change, whole chart data, zero/nonzero examples, and localization edge cases |
| `PAM-QCOH-6A` | pending | `PAM-LOCALIZATION-5A`, affine schemes | affine quasi-coherent presentation with derived basic-open and product-overlap module values; no general sheaf claim |
| `PAM-CECH-7A` | pending | `PAM-QCOH-6A`, finite affine covers | ordered varying-ring module Čech data, semilinear face restrictions, signs, repeated-face comparisons, and no cohomology overclaim |
| `PAM-GRAPH-8A` | pending | representative consumers from preceding rows | exact native operations, computation graphs, selected CAP-style whole methods, and schema-preserving categorical lowering |
| `PAM-ORACLE-9A` | pending; consumer-gated | stable native module consumer and installed Singular | optional deterministic module differential comparison with retained agreement/mismatch; never a native prerequisite |
| `PAM-CONFORMANCE-10A` | pending | all nondeferred rows | both concrete covers, focused TypeScript evidence, deterministic artifacts, final boundary audit, and proportional completion checkpoint |

Rows may be split into lettered subtranches. A row completes only after
implementation, focused positive and negative tests, proportional validation,
synchronized decisions/results, and a local checkpoint.

## Initial Decision Ledger

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-PAM-001` | accepted for audit | The first candidate represents an `A = R/I` module as `R^r/(IR^r+N_lift)` and delegates normalization to the existing module Gröbner owner. |
| `D-PAM-002` | accepted | Componentwise scalar ideal algorithms are not a module algorithm and may not replace position-aware module Gröbner computation. |
| `D-PAM-003` | accepted | Cross-ring semilinear maps are primary; same-ring linear maps specialize them at the identity algebra map. |
| `D-PAM-004` | accepted | Module base change and localization are explicit whole computations outside logical Core conversion. |
| `D-PAM-005` | accepted | Affine chart values and face restrictions derive from existing algebra maps and module base change; no manual gluing-square field is stored. |
| `D-PAM-006` | accepted | The first Čech result is a varying-ring diagram, not automatically an ordinary chain complex or sheaf-cohomology computation. |
| `D-PAM-007` | accepted | The native TypeScript engine remains authoritative for this computational profile; external CAS and formal adapters are optional consumers. |
| `D-PAM-008` | accepted | No formal module bridge, Lambdapi source change, or new Core owner is selected before a concrete module-valued formal consumer exists. |
| `D-PAM-009` | accepted | Local validated checkpoint commits are permitted on this dedicated goal branch; push, merge, publication, release, history rewriting, and cleanup are not. |
| `D-PAM-010` | accepted | The orthogonal path-cubical/strictness migration history remains excluded from this branch and from the current `main` fast-forward. |

## Validation Policy

Use proportional checks only:

- nearest focused tests during implementation;
- directly affected polynomial-module, quotient, map, localization, cover,
  graph, and engine suites at checkpoints;
- root typecheck and affected-file ESLint;
- workspace check when workspace assumptions or checkpoint boundaries are
  involved;
- exact diff, staged-diff, and `git diff --check` hygiene;
- optional installed-Singular tests only for a selected oracle row; and
- no `check:ts`, `check:all`, Lambdapi/kernel, browser, print, book, package,
  or release aggregate unless an actually affected boundary or later explicit
  instruction requires it.

Wiring focused tests into `tests/main_tests.ts` does not justify the aggregate
runner.

## Git Authorization And Checkpoints

The user authorizes this dedicated branch/worktree and local validated
checkpoint commits as the goal progresses. Every checkpoint requires a
bounded coherent tranche, synchronized living plan, proportional green
evidence, exact path-scoped staging, and review of the complete staged diff.

This authorization does not include push, merge, PR creation, publication,
release, rebase, amend, history rewriting, branch/worktree deletion, or
cleanup. The one explicitly authorized pre-goal `main` fast-forward has
already completed and does not grant any later integration authority.

## Non-Goals

- a second polynomial/module Gröbner engine;
- general modules over arbitrary non-polynomial coefficient rings;
- implicit coercion between unrelated algebra or module parents;
- automatic flatness, exactness, descent, or sheaf proofs;
- a general category of sheaves or quasi-coherent sheaves;
- a single Čech chain complex before a sound common-scalar representation;
- sheaf cohomology, derived tensor products, Tor, Ext, spectral sequences, or
  derived categories in this goal;
- optimized F4/F5 or module-signature algorithms;
- proof certificates or a formal module bridge as a native prerequisite;
- distributable-package or browser publication; or
- integration of the orthogonal path-cubical/strictness branch.

## Completion Boundary

This goal is complete when every nondeferred ledger row is implemented,
rejected with durable evidence, or explicitly deferred behind a concrete
consumer; both affine module examples execute deterministically; base change,
localization, and repeated Čech restrictions retain whole relation-checked
data; no ordinary-chain-complex or sheaf-cohomology overclaim is introduced;
the native CAS remains independent of optional formal/oracle layers; all
affected plans/tests are synchronized; and the branch is checkpointed and
clean. It is not complete merely because one quotient module or one localized
element normalizes.

## Persistent Goal Launch Prompt

```text
Continue the presented-algebra modules and affine descent goal in
/home/user1/emdash1-presented-algebra-modules-v1 on
goal/presented-algebra-modules-v3.2.

Treat docs/TYPESCRIPT_EMDASH_PRESENTED_ALGEBRA_MODULES_PLAN.md as the living
plan and delegate all evolving representation choices, row selection,
consumer scope, validation, and checkpoint details to that file. Reuse the
completed polynomial-module, affine, graph/compiler, and formal-bridge
authorities; preserve native TypeScript computation as the default; and do
not introduce a second module Gröbner engine, manual gluing squares, a formal
module adapter, or an ordinary Čech complex without a concrete sound
consumer.

Start or resume exactly one dependency-ready row, inspect current code and
worktree state before acting, run proportional focused validation without
`check:ts` unless later explicitly required, and synchronize the living plan
at every accepted, rejected, or deferred checkpoint.

The user authorizes in-scope edits and local validated checkpoint commits on
this dedicated branch. Push, merge, publication, release, history rewriting,
and cleanup remain unauthorized unless separately requested. Do not modify
main or the orthogonal path-cubical/strictness worktrees.
```
