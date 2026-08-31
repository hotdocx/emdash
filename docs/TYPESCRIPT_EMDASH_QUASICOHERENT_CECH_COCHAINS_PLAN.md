# TypeScript/emdash Varying-Ring Čech Cochains Plan

Date: 2026-08-31

Plan-ID: `TS-EMDASH-QUASICOHERENT-CECH-COCHAINS`

Status: living architecture and implementation ledger; dedicated branch and
worktree created from the completed presented-module affine-descent baseline;
`QCC-AUDIT-1A` and `QCC-COCHAIN-2A` are complete;
`QCC-DIFFERENTIAL-3A` is complete and `QCC-SQUARE-4A` is the next
dependency-ready row.

Baseline: `a3e71ae7c4bf6035c1a716a3c102a55a417e40ca`

Branch: `goal/quasicoherent-cech-cochains-v3.2`

Worktree: `/home/user1/emdash1-quasicoherent-cech-cochains-v1`

## Purpose

This plan governs the first genuine additive consumer of the completed
varying-ring affine module-descent diagram: finite Čech cochains, their
alternating differential, and computational verification that consecutive
differentials cancel.

The target path is:

```text
quasi-coherent varying-ring Cech diagram
                |
                v
degree-n heterogeneous finite cochains
                |
                v
signed face contributions in each target module
                |
                v
whole differential d^n : C^n -> C^(n+1)
                |
                v
paired repeated-face cancellations
                |
                v
computed d^(n+1)(d^n(s)) = 0
                |
                v
native operations, graphs, and portable artifacts
```

This goal constructs and evaluates a computational cochain complex over a
finite varying-ring diagram. It does not pretend that every localization is a
finitely presented module over the original algebra, and it does not yet
compute Čech cohomology.

## Authority And Prerequisites

The direct computational authority is the completed plan
`docs/TYPESCRIPT_EMDASH_PRESENTED_ALGEBRA_MODULES_PLAN.md`, especially:

- canonical presented-algebra modules and elements;
- addition, negation, zero, and equality in each localized module;
- relation-checked semilinear face maps;
- direct product-localization simplex values;
- signed affine Čech faces; and
- the existing repeated-face comparisons between both semilinear composites.

The earlier focused-CAS and affine plans remain substrate authorities. The
formal bridge is not extended in this goal. Follow the root `AGENTS.md`,
`docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`, and
`docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md` for TypeScript and persistent
goal workflow.

Local `main` was fast-forwarded only through the completed presented-module
branch before this worktree was created. The orthogonal
`goal/path-cubical-groupoidal-api-v3.2` and strictness-migration histories
remain excluded.

## Governing Principles

1. A degree is a heterogeneous finite additive product indexed by the exact
   ordered simplex family already retained by the Čech diagram.
2. A cochain component is an element of that simplex's exact localized
   presented module. Parent drift, reordering, omission, and duplication fail
   closed.
3. Cochain zero, addition, negation, and equality are componentwise. There is
   no common scalar action because component rings vary.
4. For a target simplex `J`, the differential is computed exactly as:

   ```text
   d(s)_J = sum_p (-1)^p res_(J,p)(s_(J without p)).
   ```

5. A whole differential retains every source component, face, semilinear map,
   unsigned image, sign, signed image, and final target sum.
6. Face ordering and signs come only from `AlgebraCechFace`; the cochain layer
   does not reconstruct or renumber them independently.
7. Differential additivity is computed through existing module-element
   arithmetic and semilinear application. No additive-law certificate is a
   prerequisite for execution.
8. For top positions `i < j`, the two repeated-face paths have total signs:

   ```text
   through J without i : (-1)^(i+j-1)
   through J without j : (-1)^(i+j).
   ```

   They are opposite, while the existing repeated-face comparison supplies
   equal composite semilinear maps.
9. `d²` verification retains those structural cancellation pairs and also
   computes both differentials on the supplied cochain, requiring every final
   component to be canonical zero.
10. The structural comparison is derived from stored face maps. No caller may
    supply a commuting square, sign equation, or `d²` witness.
11. A bounded diagram's final retained degree has no invented successor zero
    differential. Explicit truncation is not silently promoted to a complete
    nerve.
12. Native TypeScript remains the computational owner. A formal proof, common
    scalar presentation, or external CAS is not required.
13. Whole operations and portable artifacts are primary; convenient output
    projections derive from them.
14. Validation remains proportional. `check:ts`, `check:all`, kernel,
    browser, book, package, and release aggregates remain outside ordinary
    rows unless an actually affected boundary or later instruction requires
    one.

## Mathematical Representation

For one module-valued Čech diagram and retained degree `n`, define:

```text
C^n = product over increasing I, |I| = n+1, of M[1/f_I].
```

This is represented as a heterogeneous tuple, not as one
`AlgebraPresentedAlgebraModule`: its factors have different scalar
localizations. The tuple nevertheless has canonical additive operations
because every component module has zero, addition, negation, and equality.

For an `(n+1)`-simplex `J`, every face map has source the module at
`J without p` and target the module at `J`. Thus all signed contributions to
the `J` component live in one target module and can be added normally.

This representation is sufficient for differential evaluation and `d²`
cancellation. It deliberately does not supply kernels, cokernels, or
cohomology objects for heterogeneous degrees.

## Proposed Implementation Sequence

### 1. Owner and orientation audit

Trace the existing degree ordering, face ordering, sign convention,
semilinear endpoints, and repeated-face comparison orientation. Permanently
test the binary convention:

```text
d(a_0,a_1)_[0,1] = res_from_[1](a_1) - res_from_[0](a_0).
```

Verify the two total signs for every pair `i < j` in the ternary top simplex.
The audit must reject any independent reindexing convention that disagrees
with the retained affine faces.

### 2. Heterogeneous cochain degrees and elements

Implement a stable parent for one diagram degree and a cochain element with
one component per ordered simplex. Provide:

- zero;
- addition and negation;
- subtraction if useful to consumers;
- canonical equality;
- component observation by position and simplex indices;
- schemas and deterministic serialization; and
- precise parent/order/arity diagnostics.

The degree parent identity contains the underlying presentation-module
identity, ordered simplex indices and localized module identities, and the
degree. It does not claim a common module parent.

### 3. Whole differential evaluation

Implement `d^n` only when degree `n+1` is retained. For every target simplex,
locate its faces in stored order, fetch the aligned source cochain component,
apply the retained semilinear restriction, negate exactly the odd-position
images, and add them in the target module.

Return a whole result retaining:

- source and target degrees;
- input and output cochains;
- one ordered target computation per target simplex;
- all signed contribution records; and
- additivity comparisons requested by focused consumers.

### 4. Structural and evaluated differential-square cancellation

For every repeated-face comparison, construct one cancellation record with:

- top and lower simplex indices;
- removed positions `i < j`;
- both intermediate simplices;
- both stored composite maps;
- both computed total signs;
- equality of the unsigned composite maps;
- opposition of signs; and
- the resulting zero pair on the supplied lower component.

Then compute `d^(n+1)(d^n(s))` and require the resulting cochain to be zero.
The whole square result retains both differential computations and all
cancellation records.

### 5. Native operations and computation graphs

For a fixed diagram/degree, expose exact operations for:

- cochain differential evaluation; and
- differential-square evaluation where degree `n+2` exists.

Use the ordinary reference engine and `AlgebraComputationGraph`. Retain exact
schemas and management context without adding global Core conversion or a
new category doctrine.

### 6. Portable artifacts and final examples

Retain deterministic artifacts for:

1. the free rank-one module on `A = Q[x]` over `D(x),D(1-x)`, including a
   diagonal cochain with zero differential and an asymmetric cochain with a
   nonzero differential;
2. the existing `A/(x)` support example; and
3. the free rank-one module on `A = Q[x,y]` over
   `D(x),D(y),D(1-x-y)` through degree two, with computed
   `d^1(d^0(s)) = 0` and all three structural cancellation pairs.

Direct construction and native graph execution must serialize identically.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `QCC-PLAN-0` | complete | completed presented-module affine descent and reviewed continuation | this living plan, isolated branch/worktree, baseline, representation, staged rows, validation, and Git limits |
| `QCC-AUDIT-1A` | complete; orientation probe and 29-test baseline green | existing module-valued Čech diagram | exact owner map in `TYPESCRIPT_EMDASH_QUASICOHERENT_CECH_COCHAINS_OWNER_AUDIT.md`, binary differential convention, ternary sign pairs, degree-parent decision, and truncation boundary |
| `QCC-COCHAIN-2A` | complete; proportional-green at `f023d7b` | `QCC-AUDIT-1A` | stable heterogeneous degree parents, aligned cochain elements, global-element construction, zero/addition/negation/subtraction/equality, positional/index lookup, schemas/serialization, and complete diagnostics |
| `QCC-DIFFERENTIAL-3A` | complete; proportional-green at `6b0889e` | `QCC-COCHAIN-2A` | whole alternating differential with exact endpoint lookup, retained ordered target/contribution data, binary orientation, global-section cancellation, additive/zero/negation comparisons, serialization, and truncation failure |
| `QCC-SQUARE-4A` | pending; next selected row | `QCC-DIFFERENTIAL-3A`, repeated-face comparisons | structural sign/map cancellation records and evaluated `d² = 0` for every available degree |
| `QCC-GRAPH-5A` | pending | `QCC-SQUARE-4A` | exact native differential/square operations, fixed-degree schemas, reference-engine and graph execution |
| `QCC-CONFORMANCE-6A` | pending | all preceding rows | three concrete examples, deterministic direct/graph artifacts, final proportional validation, completion audit, and clean checkpoint |

Rows may be split into lettered subtranches. A row completes only after
implementation, focused positive and negative tests, proportional validation,
synchronized decisions/results, and a local checkpoint.

## Initial Decision Ledger

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-QCC-001` | accepted | Cochain degrees are heterogeneous finite additive products, not falsely presented modules over one scalar algebra. |
| `D-QCC-002` | accepted | Cochain component order is exactly the existing ordered simplex family for that degree. |
| `D-QCC-003` | accepted | Differential faces and signs come exclusively from the retained affine Čech data. |
| `D-QCC-004` | accepted | Whole differential results retain every contribution and target sum; a projected output tuple alone is insufficient. |
| `D-QCC-005` | accepted | `d²` uses existing equal repeated-face composites plus opposite total signs; no manual coherence field or equality witness is accepted. |
| `D-QCC-006` | accepted | The final retained degree has no successor differential because the nerve may be explicitly truncated. |
| `D-QCC-007` | accepted | The goal ends before kernels, cokernels, cohomology, restriction-of-scalars finite presentations, or sheaf/descent theorems. |
| `D-QCC-008` | accepted | Native TypeScript and ordinary computation graphs remain the implementation boundary; no formal bridge or external CAS is selected. |
| `D-QCC-009` | accepted | Local validated checkpoint commits are permitted on this dedicated branch; push, merge, publication, release, history rewriting, and cleanup are not. |
| `D-QCC-010` | accepted | The orthogonal path-cubical/strictness histories remain excluded from this branch and from the pre-goal `main` fast-forward. |
| `D-QCC-011` | accepted | The binary stored orientation is `d(a₀,a₁)=res(a₁)−res(a₀)`; face-array position is not reused as the source cochain position. |
| `D-QCC-012` | accepted | For `i<j`, the first stored repeated-face route has sign `(-1)^(i+j−1)` and the second `(-1)^(i+j)`, exactly matching all three ternary comparisons. |
| `D-QCC-013` | accepted | A cochain-degree identity is the diagram presentation/cover shape, degree, ordered simplex indices, and localized module parent identities; it carries no common scalar parent. |
| `D-QCC-014` | accepted | A cochain contains one canonical presented-module element per exact ordered simplex; component schemas are selected positionally from the degree owner. |
| `D-QCC-015` | accepted | Global-element cochains are derived by applying every simplex's retained ambient base-change unit to one element of the presentation module. |
| `D-QCC-016` | accepted | Heterogeneous cochains expose only additive operations and equality; no cross-component scalar action or common module parent is introduced. |
| `D-QCC-017` | accepted | Differential target faces are filtered by exact codomain simplex identity and required to remain in removed-position order; source components are located separately by domain indices. |
| `D-QCC-018` | accepted | Odd face images are negated in their target module before the ordered sum. The whole result retains unsigned and signed images rather than only the output tuple. |
| `D-QCC-019` | accepted | Zero, negation, and binary additivity are computed comparisons over canonical cochains. The bounded top degree raises `NO_SUCCESSOR_DEGREE` rather than receiving a fabricated zero differential. |

## `QCC-DIFFERENTIAL-3A` Result

Whole alternating Čech differentials are implemented in
`src/v3_2/algebra_quasicoherent_differential.ts`. For every retained target
simplex, the implementation selects its exact stored incoming faces, verifies
removed-position ordering, finds source cochain components by the face-domain
indices, applies each semilinear restriction, negates odd contributions, and
sums inside the target localized module.

The whole value retains source/target degree parents, input/output cochains,
one computation per target simplex, and every face, source position/element,
unsigned image, sign, signed image, and target sum. Separate computations
check additivity, zero preservation, and compatibility with negation.

Five focused tests freeze the binary `res(a₁)−res(a₀)` orientation and source
positions, show that a diagonal/global cochain has zero differential while an
asymmetric cochain does not, check ternary additivity/zero/negation and all
target contribution signs, verify deterministic serialization, and reject a
differential past the retained top degree. Together with cochain, varying-ring
Čech, and semilinear-map suites, 22 tests pass, followed by workspace check,
root typecheck, affected lint, and diff hygiene. No repository-wide aggregate
or Lambdapi check was run.

Semantic checkpoint: `6b0889e` (`cochains: add alternating Cech differential`).

## `QCC-COCHAIN-2A` Result

Heterogeneous Čech degree parents and cochain elements are implemented in
`src/v3_2/algebra_quasicoherent_cochain.ts`. A degree identity retains the
diagram presentation, cover shape, degree, ordered simplex indices, and each
localized module identity. It deliberately has no common scalar algebra.

A cochain constructor checks exact arity and every component against the
module at the same ordered simplex. Componentwise zero, addition, negation,
subtraction, equality, and zero testing reuse canonical presented-module
element operations. Components are observable by bounded position or exact
simplex indices. A global ambient module element maps into any retained degree
through the simplex base-change units.

Five focused tests cover binary/ternary degree ordering and identity, global
element transport, all additive operations, positional/index observation,
schemas/serialization, and degree/arity/order/module/lookup/global-parent
failures. Together with varying-ring Čech, presented-module, and semilinear-
map suites, 25 tests pass, followed by workspace check, root typecheck,
affected lint, and diff hygiene. No repository-wide aggregate or Lambdapi
check was run.

Semantic checkpoint: `f023d7b` (`cochains: add heterogeneous Cech degrees`).

## `QCC-AUDIT-1A` Result

The complete owner/orientation audit is recorded in
`docs/TYPESCRIPT_EMDASH_QUASICOHERENT_CECH_COCHAINS_OWNER_AUDIT.md`. It accepts
the active degree and face ordering without an adapter and freezes the binary
differential as `res(a₁)−res(a₀)`.

The ternary audit locates both paths for every removed-position pair and
measures total signs `(+,-)`, `(-,+)`, and `(+,-)`. These are the general
`(-1)^(i+j−1)` and `(-1)^(i+j)` pair. The existing repeated-face owner already
supplies canonical equality of the corresponding unsigned semilinear maps.

The unchanged quasi-coherent Čech/chart, semilinear-map, presented-module, and
descent-artifact suites pass 29/29 after worktree bootstrap. No source file or
Lambdapi authority changed in the audit.

## Validation Policy

Use proportional checks only:

- nearest focused cochain/differential/square tests during implementation;
- directly affected quasi-coherent Čech, semilinear-map, presented-module,
  graph, engine, and artifact suites at checkpoints;
- workspace check at bounded checkpoints;
- root typecheck and affected-file ESLint;
- exact diff, staged-diff, and `git diff --check` hygiene; and
- no `check:ts`, `check:all`, Lambdapi/kernel, browser, print, book, package,
  or release aggregate unless an actually affected boundary or later explicit
  instruction requires it.

Wiring focused tests into `tests/main_tests.ts` does not itself justify the
aggregate runner.

## Git Authorization And Checkpoints

The user authorizes this dedicated branch/worktree and local validated
checkpoint commits as the goal progresses. Every checkpoint requires a
bounded coherent tranche, synchronized living plan, proportional green
evidence, exact path-scoped staging, and review of the staged diff.

This authorization does not include push, merge, PR creation, publication,
release, rebase, amend, history rewriting, branch/worktree deletion, or
cleanup. The explicitly authorized pre-goal `main` fast-forward is complete
and grants no later integration authority.

## Non-Goals

- treating localizations as finitely presented modules over the base algebra;
- a common scalar-module parent for heterogeneous cochain degrees;
- kernels, cokernels, cohomology, exactness, or descent effectiveness;
- general sheaf or quasi-coherent-sheaf categories;
- derived tensor products, Tor, Ext, DG modules, or spectral sequences;
- formal proof certificates, a formal module bridge, or new Lambdapi/Core
  owners;
- distributable-package or browser publication; or
- integration of path-cubical/strictness work.

## Completion Boundary

This goal is complete when every ledger row is implemented, rejected with
durable evidence, or explicitly deferred behind a concrete consumer; the
binary differential convention is frozen; degree elements and whole
differentials are parent/order safe; every ternary repeated face has an
opposite-sign cancellation record; `d²` evaluates to zero on the selected
cochains; direct and graph artifacts agree; no common-scalar/cohomology
overclaim is introduced; proportional gates and the living plan are
synchronized; and the branch is checkpointed and clean.

## Persistent Goal Launch Prompt

```text
Continue the varying-ring affine Cech cochains goal in
/home/user1/emdash1-quasicoherent-cech-cochains-v1 on
goal/quasicoherent-cech-cochains-v3.2.

Treat docs/TYPESCRIPT_EMDASH_QUASICOHERENT_CECH_COCHAINS_PLAN.md as the living
plan and delegate all evolving degree/cochain representation, differential
orientation, cancellation design, row selection, validation, and checkpoint
details to that file. Reuse the completed presented-module affine-descent
owners and their stored face comparisons; preserve heterogeneous scalar
rings; and do not introduce manual coherence squares, a false common module
parent, cohomology, a formal adapter, or cubical/strictness history.

Start or resume exactly one dependency-ready row, inspect current code and
worktree state before acting, run proportional focused validation without
`check:ts` unless later explicitly required, and synchronize the living plan
at every accepted, rejected, or deferred checkpoint.

The user authorizes in-scope edits and local validated checkpoint commits on
this dedicated branch. Push, merge, publication, release, history rewriting,
and cleanup remain unauthorized unless separately requested. Do not modify
main or the orthogonal path-cubical/strictness worktrees.
```
