# TypeScript/emdash Formal Presentation Morphisms And CAS Delegation Plan

Date: 2026-08-31

Plan-ID: `TS-EMDASH-FORMAL-PRESENTATION-MORPHISMS`

Status: implementation complete on a dedicated branch/worktree; final
conformance/documentation checkpoint pending.

Baseline: `2c56d41b6b152fd912feeb517a2bae68c9ced64b`

Branch: `goal/formal-presentation-morphisms-v3.2`

Worktree: `/home/user1/emdash1-formal-presentation-morphisms-v1`

Decision-Response-Evidence:

- `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a05971-70a2-7560-b2cb-ad99bae3c800`

## Purpose

This plan governs the missing morphism layer between the completed formal
finite-presentation calculus and future complexes, quotient semantics, and
homology:

```text
formal column matrices and presentation equations
  -> fixed-ring presentation objects
  -> computed relation witnesses for candidate maps
  -> computed congruence between map representatives
  -> explicit Core equations and classified adoption
  -> identity/composition and categorical compatibility
  -> one chain-map-square capstone
  -> portable artifacts and live backend conformance.
```

The goal is a concrete proof--CAS bridge extension, not an abstract module,
quotient type, formal Abelian category, or homology theory. Direct matrices
remain the concrete backend beneath the existing CAP-like category, doctrine,
tower, reinterpretation, and compiler layers.

## Operational Baseline

The completed finite-module branch was fast-forwarded to the historical
`main` worktree before this branch was created. `main` and this branch share
the exact baseline `2c56d41`. Orthogonal path-cubical and strictness-migration
branches remain excluded.

The root and nested repository guidance remain mandatory. Local validated
checkpoint commits are authorized on this dedicated branch. This does not
authorize push, merge, publication, release, PR creation, history rewriting,
branch deletion, worktree removal, or integration of orthogonal branches.

## Why Presentation Morphisms Come Next

For presentations over one commutative ring,

```text
P = (g_P, r_P, R_P : Matrix(R,g_P,r_P))
Q = (g_Q, r_Q, R_Q : Matrix(R,g_Q,r_Q)),
```

a candidate map on generators is a matrix

```text
F : Matrix(R,g_Q,g_P).
```

It respects the source relations when there is a retained relation matrix

```text
W : Matrix(R,r_Q,r_P)
```

with the exact equation, oriented to match the existing membership owner,

```text
R_Q o W = F o R_P.
```

This is the computational `relationWitness` architecture already used by the
field-linear CAS. The polynomial/presented-algebra and formal bridge layers do
not yet retain this whole witness.

Two representative matrices induce the same map modulo the target relations
when there is

```text
H : Matrix(R,r_Q,g_P)
```

with

```text
R_Q o H = F - G.
```

This supplies useful quotient-style reasoning without constructing a quotient
carrier. It also retains the computational coefficient data that a premature
quotient would hide.

## Why Quotient Semantics Are Deferred

The current `CommRingPresentationAgreement` is intentionally not generally
proposition-valued: two coefficient witnesses may differ by a syzygy. Turning
agreement immediately into path equality would require a substantive choice
among:

- a setoid quotient;
- a propositionally truncated quotient;
- an action groupoid retaining syzygy automorphisms;
- a HIT quotient; or
- a categorical cokernel/Freyd interpretation.

None is needed to decide relation preservation or representative congruence.
Those questions reduce directly to module membership and explicit matrix
equations. The selected quotient semantics should therefore be introduced
only when a later module-equality, kernel/cokernel, or homology consumer needs
it.

## Existing Substrate And Exact Gaps

The completed formal owner
`emdash2/emdash3_2_commutative_algebra_finite_modules.lp` provides:

- `CommRingVector` and column-oriented `CommRingMatrix`;
- vector zero/addition/negation/subtraction/scaling;
- matrix action, zero, and composition;
- `CommRingPresentationAgreement`;
- `CommRingMatrixSyzygy`; and
- `CommRingMatrixCompositeZero`.

The completed TypeScript bridge provides exact signatures, parent-aware
vector/matrix reification, whole membership, syzygy and bounded-resolution
delegation, classified assumption sources, deterministic artifacts, and one
presented-module categorical lowering.

The computational layer additionally provides:

- `AlgebraPolynomialModuleMap`, application, identity, composition, and zero
  detection for polynomial free modules;
- `AlgebraPresentedPolynomialModule` and whole Gröbner membership;
- `AlgebraPresentedAlgebraModule` with combined algebra-action and user
  relations;
- fixed- and varying-ring presented-module maps at the public category layer;
- field-linear `AlgebraModuleMorphism` with an explicit `relationWitness`;
- bounded field-linear complexes, chain maps, kernels, cokernels, and homology;
  and
- typed operations, computation graphs, category methods, towers,
  reinterpretations, and compilation.

The exact gaps are:

- no formal presentation object or presentation-morphism classifier;
- no formal map-representative congruence classifier;
- no polynomial/presented-algebra whole computation that retains `W`;
- no whole computation that retains `H` for representative agreement;
- no formal bridge adapter for either equation; and
- no formal chain-map square beyond adjacent differential zero.

## Formal Design

### Matrix operations

Add only the transparent matrix operations required by the consumers:

```text
A + B
-A
A - B
I_n                         // only if an identity consumer needs it
```

They must reuse finite-family/vector owners. Ring associativity,
distributivity, units, and matrix-algebra laws remain theorem-level paths. No
rewrite or unification rule is presumed. Identity and composition laws are
implemented only as far as a concrete presentation-morphism consumer needs
them and only after focused proof/projection audits.

### Presentation object

The intended internal package is the transparent dependent data

```text
CommRingPresentation(R)
  := Sigma generators : Nat,
       Sigma relations : Nat,
         Matrix(R,generators,relations).
```

Named projections may expose generator rank, relation rank, and relation
matrix. They are semantic views, not new independent owners.

### Relation-preserving morphism

For `P,Q : CommRingPresentation(R)`, define retained data equivalent to

```text
CommRingPresentationMorphism(P,Q)
  := Sigma F : Matrix(R,g_Q,g_P),
       Sigma W : Matrix(R,r_Q,r_P),
         R_Q o W = F o R_P.
```

`W` is constructive relation data, not a manually authored coherence square.
The computational operation should derive it column by column from whole
target-relation membership. Its equality law becomes a checked or explicitly
adopted exact Core claim.

### Representative congruence

For two candidate generator maps `F,G`, define

```text
CommRingPresentationMorphismAgreement(P,Q,F,G)
  := Sigma H : Matrix(R,r_Q,g_P),
       R_Q o H = F - G.
```

This is explicit agreement data, not judgmental equality, a quotient path, or
a proof that all such witnesses are equal. A negative computation retains at
least one canonical nonzero remainder and leaves the goal open.

### Chain-map-square capstone

For free differential matrices and component matrices, expose the exact
classifier

```text
e_i o F_i = F_(i-1) o d_i.
```

The components are input data; the square is computed and checked. No
independent hand-written square field is accepted as evidence. A whole
arbitrary-length formal chain-complex category is not required by this goal;
the capstone establishes the next bounded-complex continuation using the same
matrix-equation bridge.

## Computational Design

The first implementation is fixed-ring and polynomial/presentation based.
For one candidate map `F`, a whole result retains:

- source and target presentations;
- the candidate generator map;
- every image of a source relation;
- every target-basis membership computation;
- coefficients relative to the original target relation columns;
- the assembled relation witness `W`;
- all remainders and reduction counts; and
- the exact preservation status.

The public `AlgebraPresentedAlgebraModuleSemilinearMap` need not be redesigned
merely to store these coefficients. A bridge-oriented whole realization may
retain the existing public map together with the computed witness data.

For representative agreement, a whole result similarly retains every column
of `F-G`, every membership result, the assembled `H`, and all remainders.

Foreign polynomial rings, free-module parents, ranks, term orders, relation
orders, and map endpoints must be rejected. Equivalent normalized inputs must
produce identical deterministic serialization.

Varying-ring semilinear maps are deferred. They additionally require formal
structured-ring maps and scalar transport; fixed-ring presentation morphisms
must be settled first.

## Proof--CAS Delegation

The existing generic request, execution, workflow, adoption, classified
assumption-source, receipt, and live-probe owners are reused unchanged.

Positive relation preservation targets the exact equation

```text
R_Q o W = F o R_P.
```

Positive representative agreement targets

```text
R_Q o H = F - G.
```

Each adapter must require:

- the current realization profile;
- exact computational parent and dimension identity;
- exact selected whole output;
- exact Core goal identity; and
- successful membership for every required column.

Negative outputs are observations and cannot be adopted as positive claims.
Batch adoption appends every selected equation independently in deterministic
order with classification `computed-equation`.

## CAP/homalg Architectural Contract

This goal implements the concrete morphism dictionary beneath categorical
abstraction:

```text
ring and module algorithms
  -> presentation matrices and relation witnesses
  -> typed whole operations and graphs
  -> direct presented-module category
  -> doctrines, towers, reinterpretations, compiler
  -> explicit formal realization and adoption.
```

Generic categorical algorithms must continue depending on operation roles and
category interfaces, not on matrix internals. At least one representative
identity/composition or map-action program must lower through the existing
categorical compiler and agree with the direct computation and formal
orientation.

A formal `Cat` of presentations is audit-gated rather than promised. The
current Lambdapi nucleus has no generic record constructor that turns arbitrary
object/Hom/identity/composition data into `Cat`; forcing a new category head
would require a separate full owner/rule/projection design. The formal
presentation and morphism packages remain useful and internal without that
overclaim.

## Proposed Implementation Sequence

1. Audit matrix algebra, polynomial maps, presentation order, and formal
   package/projection feasibility.
2. Add transparent matrix addition/negation/subtraction and only the required
   identity/law support.
3. Add formal presentation, morphism, and representative-agreement packages.
4. Implement whole polynomial relation-witness computation.
5. Implement whole representative-congruence computation.
6. Add exact LF signature mirrors and parent-aware Core reification.
7. Delegate positive/negative map and agreement equations; batch classified
   adoptions and portable artifacts.
8. Connect identity/composition and one categorical compiler consumer to the
   same representation.
9. Add one computed chain-map-square capstone.
10. Register formal owners, update standing documentation, and pass focused
    live Lambdapi conformance.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `FPMAP-PLAN-0` | in progress | completed finite-presentation bridge at `2c56d41` and reviewed continuation | living plan, isolated branch/worktree, exact baseline, mathematics, validation, Git limits |
| `FPMAP-AUDIT-1A` | complete; checkpoint `6c4ea6b` | plan | exact formal/CAS orientation, missing owners, matrix-law burden, selected fixed-ring model, category boundary |
| `FPMAP-MATRIX-2A` | complete; checkpoint `d5bae5d` | audit | transparent matrix add/neg/sub and narrowly required identity/law support, positive/noncollapse consumers |
| `FPMAP-FORMAL-3A` | complete; checkpoint `d5bae5d` | matrix | formal presentation, relation-preserving morphism, representative agreement, and chain-square classifiers without quotient overclaim |
| `FPMAP-WITNESS-4A` | complete; checkpoint `f90bb4d` | formal | whole polynomial relation-witness computation with coefficients/remainders and positive/negative cases |
| `FPMAP-CONGRUENCE-5A` | complete; checkpoint `f90bb4d` | witness | whole `F-G` target-relation membership and assembled `H`, including negative remainder |
| `FPMAP-REIFY-6A` | complete; checkpoint `9299126` | formal/computational owners | exact signatures, presentation/map/witness reification, dimension/parent/order diagnostics |
| `FPMAP-DELEGATE-7A` | complete; checkpoint `9299126` | reifier | exact-target adapters, positive/negative workflows, classified batch source, deterministic artifact |
| `FPMAP-CATEGORY-8A` | complete; checkpoint `9299126` | witness/congruence | identity/composition and representative categorical lowering/direct agreement; no forced formal `Cat` |
| `FPMAP-CHAIN-9A` | complete; checkpoint `9299126` | map equations | computed chain-map-square capstone using components rather than manually supplied coherence |
| `FPMAP-CONFORMANCE-10A` | complete; final checkpoint pending | all active rows | registration, standing docs, affected checks/lint, live emitted-Core Lambdapi acceptance, proportional final audit |

Rows may be split, rejected, or deferred only with durable evidence and a
synchronized plan. Each completed row requires focused positive/negative
tests, proportional validation, and a local checkpoint.

## Initial Decisions

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-FPMAP-001` | accepted | Presentation morphisms and representative congruence are the next missing formal bridge layer. |
| `D-FPMAP-002` | accepted | The first computational model is fixed-ring; varying-ring semilinear transport is later. |
| `D-FPMAP-003` | accepted | A relation witness `W` is computed constructive data; its equation is not manually supplied evidence. |
| `D-FPMAP-004` | accepted | Representative agreement retains `H` and its equation rather than claiming quotient equality. |
| `D-FPMAP-005` | accepted | Quotient/setoid/HIT/action-groupoid/Freyd semantics remain consumer-gated. |
| `D-FPMAP-006` | accepted | Matrix equations and whole membership results remain primary; Boolean facades are derived. |
| `D-FPMAP-007` | accepted | No rewrite or unification rule is presumed; transparent definitions and theorem-level paths are preferred. |
| `D-FPMAP-008` | accepted | A chain-map square is a computed consequence of components, not an independent hand-written square field. |
| `D-FPMAP-009` | accepted | A formal presentation `Cat` is not required unless the owner audit finds a small justified construction. |
| `D-FPMAP-010` | accepted | Direct matrices remain the backend beneath category/doctrine/tower/compiler abstraction. |
| `D-FPMAP-011` | accepted | Local validated checkpoints are authorized; push, merge, publication, release, history rewriting, and cleanup are not. |
| `D-FPMAP-012` | accepted | Orthogonal path-cubical/strictness histories remain excluded from the baseline. |
| `D-FPMAP-013` | accepted after audit | Relation preservation is oriented `R_Q o W = F o R_P`, and representative agreement is oriented `R_Q o H = F-G`, matching columnwise module-membership output without an equality-symmetry adapter. |
| `D-FPMAP-014` | accepted after audit | `AlgebraPresentedPolynomialModule.relationBasis` retains transformations back to `relations.generators`, so membership coefficients assemble witnesses against the original ordered relation matrix rather than the reduced basis order. |
| `D-FPMAP-015` | accepted after audit | Matrix add/neg/sub and transparent Sigma presentation packages suffice for the first formal equations; matrix identity and theorem-level category laws remain consumer-gated. |
| `D-FPMAP-016` | accepted during computation | Relation-coefficient free modules use deterministic term-over-position parents; this auxiliary order does not replace the original ordered relation columns or the ambient module's term order. |
| `D-FPMAP-017` | accepted during computation | A negative map still retains the candidate coefficient matrix assembled from division, but only all-zero remainders plus the independently rechecked whole matrix equation set `preservesRelations`. |
| `D-FPMAP-018` | accepted during computation | Representative agreement subtracts maps columnwise, computes every target membership, assembles `H`, and independently checks `R_Q o H = F-G`; no quotient equality is produced. |
| `D-FPMAP-019` | accepted during computation | The first chain-square computation is exact polynomial-map equality after both composites; it retains both sides and does not accept a square witness as input. |
| `D-FPMAP-020` | accepted during operation exposure | Relation witnesses, representative agreement, and chain squares are three typed whole operations sharing one reference-engine bundle; their canonical serializers retain maps, memberships, witnesses, both equation sides, status, and reduction counts. |
| `D-FPMAP-021` | accepted during reification | Explicit Core targets fix the CAS-selected matrices and ask only for their equality law; adopting a whole existential package would hide `F`, `W`, or `H` behind an opaque assumption. |
| `D-FPMAP-022` | accepted during reification | The exact LF mirror unfolds matrix classifiers to nested `FiniteFamily` and adds only the new matrix-subtraction signature; composition and equality reuse the completed finite-module signature surface. |
| `D-FPMAP-023` | accepted during delegation | All three adapters require current profiles, exact reconstructed Core targets, exact selected whole-output bytes, and a successful result projection; failed maps and squares remain unadoptable observations. |
| `D-FPMAP-024` | accepted during batch usability | One batch adopts morphisms, agreements, then chain squares, with one independently classified assumption per equation and deterministic portable serialization. |
| `D-FPMAP-025` | accepted during category compatibility | A fixed-ring public presented-module map is lifted to its polynomial generator matrix, recomputes `W`, reifies the same law, and retains direct/compiled map-action agreement; no formal `Cat` is asserted. |
| `D-FPMAP-026` | accepted during conformance | Live emission imports the active presentation owner and maps only the new matrix-subtraction signature in addition to inherited formal bindings; all three exact equation targets check in Lambdapi. |
| `D-FPMAP-027` | accepted during conformance | The owner and reviewer are registered; health is synchronized as an honest no-check 332-target snapshot under the established scoped-validation policy. |

## Initial Formal Result

The rule-free one-way module
`emdash2/emdash3_2_commutative_algebra_presentations.lp` now implements the
selected formal layer. Matrix addition recurses over the ordered columns,
matrix negation maps vector negation over those columns, and subtraction is
their transparent composite. No matrix identity was added because neither
selected membership-oriented equation consumes it.

`CommRingPresentation(R)` is the transparent nested Sigma of generator rank,
relation rank, and relation matrix. Named projections expose those three
fields. `CommRingPresentationMorphism(P,Q)` retains `F`, `W`, and the equation
`R_Q o W = F o R_P`; `CommRingPresentationMorphismAgreement(P,Q,F,G)` retains
`H` and `R_Q o H = F-G`. `CommRingChainMapSquare` records only the exact square
computed from four selected matrices.

The reviewer exposes visible one-column matrix addition/subtraction, all three
presentation projections, and explicit constructors for morphisms, agreement,
and a chain square. A visible subtraction remains distinct from the zero
matrix. Owner and reviewer pass bounded Lambdapi checking; warning-enabled
checking finds no diagnostic located in the new module, and its strict LHS
audit is empty because it declares no rule or unifier.

## Initial Computational Result

`src/v3_2/algebra_polynomial_presentation_morphism.ts` now owns the whole
fixed-ring computations. For a candidate `F`, it applies `F` to every original
source relation, reduces each image by the target Gröbner basis, retains every
membership, and assembles the original-target-order coefficients as the
columns of `W`. It then reconstructs and compares the whole maps
`R_Q o W` and `F o R_P`; the Boolean preservation projection is secondary.

Representative agreement subtracts `F-G` columnwise, retains every target
membership and remainder, assembles `H`, and compares `R_Q o H` with the whole
difference map. Both positive and negative results preserve coefficients,
remainders, basis quotients through their memberships, and total reduction
steps.

The same file provides exact polynomial-map equality/subtraction and the
chain-square capstone computation. Focused tests cover a nontrivial valid
relation witness, failed relation preservation with nonzero remainder, valid
and invalid representative agreement, a commuting and noncommuting chain
square, and foreign map endpoints. The thirteen directly affected polynomial
module/presentation tests, root typecheck, and affected lint pass.

The native reference bundle exposes morphism, agreement, and chain-square
operations with separate structural input/output schemas and algorithms. A
focused graph lowers the relation-witness operation without projection or
fusion, and its retained whole output serializes byte-for-byte identically to
direct operation execution. The directly affected graph and presentation
suites pass.

## Reification, Delegation, And Category Result

The formal reifier now emits the selected target relation matrix, candidate
map, computed `W` or `H`, both equation sides, and exact equality classifier.
Matrix classifiers use the transparent nested-`FiniteFamily` body; the exact
signature extension adds only `comm_ring_matrix_sub`, while composition,
equality, ring operations, Nat, and finite-family constructors reuse the
completed finite-module bridge.

Morphism, agreement, and chain-square adapters recompute their whole outputs
through the native operations and compare canonical bytes with the selected
realization. They also reconstruct the Core target and reject goal drift.
Positive outputs become explicit `computed-equation` assumptions; a failed
relation map retains its nonzero remainder and cannot be adopted.

The batch usability owner accepts ordered collections of all three equations,
adopts them in morphism/agreement/chain order, and returns a deterministic
artifact containing the complete classified source, selected computation
bytes, and Core claims.

The category compatibility consumer starts from a validated fixed-ring public
presented-module map, extracts its polynomial generator matrix, recomputes the
ordered relation witness, and reifies the same equation. A nontrivial composed
endomorphism then executes through the existing categorical compiler and
agrees with direct map action. Fourteen focused bridge/category tests, root
typecheck, and affected lint pass. A formal category of presentations remains
deliberately unclaimed.

## Conformance Result

The new formal owner and reviewer are registered in the maintained target
inventories. Quiet and warning-enabled focused checks pass, no diagnostic is
located in the new owner, and strict LHS audit reports zero clauses because
the module has no rewrite or unification rule.

Exact emitted Core for relation preservation, representative agreement, and
the chain-map square passes both the TypeScript Core checker and a live bounded
Lambdapi probe against
`emdash3_2_commutative_algebra_presentations`. Positive workflows yield three
separate computed-equation assumptions; the negative relation map remains an
unadoptable observation with a retained nonzero remainder.

Standing current-status, Foundations, canonical-syntax, and report-index
documentation now records the selected orientations and nonclaims. The strict
catalog remains synchronized. Health records the new owner and reviewer in an
honest no-check 332-target source snapshot; no repository-wide formal timing
claim is introduced.

## Validation Policy

- Documentation-only changes receive exact diff, link, registry, and Markdown
  hygiene checks.
- TypeScript changes receive workspace validation, root typecheck, affected
  lint, and focused map/module/graph/category tests.
- Formal changes follow the complete nested Lambdapi SOP, including focused
  owner/example checks, warning-location comparison, strict LHS audit if rules
  exist, registration, catalog/health synchronization, and live emitted-Core
  probes.
- Every Lambdapi target is bounded to at most 90 seconds.
- The integrated baseline's scoped-validation policy remains active: avoid
  repository-wide TypeScript, formal, book, print, package, or release
  aggregates beyond an actually affected integration boundary.
- Carry forward recent green evidence for unchanged boundaries.

## Non-Goals

- a semantic quotient module or equality in a quotient carrier;
- proof certificates or proving the CAS correct;
- varying-ring semilinear presentation morphisms;
- a forced formal category head for presentations;
- a complete arbitrary-length formal chain-complex category;
- kernels, cokernels, exactness, homology, Tor, Ext, or spectral sequences;
- Čech differentials or cohomology;
- GAP/CAP API compatibility;
- parser, browser/public-package publication, hosted service, or external CAS
  deployment; or
- push, merge, publication, release, PR creation, history rewriting, branch
  deletion, or worktree cleanup.

## Completion Boundary

The goal completes when every active ledger row is implemented,
audit-rejected, or explicitly deferred behind a concrete prerequisite;
relation witnesses and representative congruence compute as whole retained
results; their exact equations flow through explicit Core and classified
adoption; positive and negative cases remain distinct; one categorical
consumer and one chain-square capstone use the same representation; portable
artifacts and live Lambdapi conformance pass; standing documentation and
registries are synchronized; and every bounded tranche is checkpointed.

## Persistent `/goal` Launch Prompt

Work in `/home/user1/emdash1-formal-presentation-morphisms-v1` on
`goal/formal-presentation-morphisms-v3.2`. Implement the formal fixed-ring
presentation-morphism, representative-congruence, proof--CAS delegation,
categorical compatibility, and chain-square objective with every evolving
owner, orientation, matrix-law choice, equation, reifier, adapter, trust
classification, artifact, validation result, checkpoint, and completion
condition delegated to this plan. Preserve baseline `2c56d41`, exclude
orthogonal path-cubical/strictness work, and re-read current source/SOP/plan on
every continuation. Treat direct matrices as the concrete backend beneath the
existing CAP-like abstraction; do not claim quotient-module equality, a
formal presentation category, exactness, or homology. Add formal mathematics
only under the nested Lambdapi SOP, use proportional affected checks, make
only local validated checkpoint commits, and do not push, merge, publish,
release, rewrite history, remove worktrees, or broaden unrelated formal/kernel
semantics.
