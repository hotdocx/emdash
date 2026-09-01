# TypeScript/emdash Formal Bounded Free Complexes And Chain Maps Plan

Date: 2026-09-01

Plan-ID: `TS-EMDASH-FORMAL-BOUNDED-FREE-COMPLEXES`

Status: active living plan on a dedicated branch/worktree; reviewed recursive
design, owner-position feasibility probe pending.

Baseline: `c9d8e5ff1c91c1292fa0548b895e3183a0a8657c`

Branch: `goal/formal-bounded-free-complexes-v3.2`

Worktree: `/home/user1/emdash1-formal-bounded-free-complexes-v1`

Decision-Response-Evidence:

- `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a05b91-8d99-7993-800c-c2884f4a9698`

## Purpose

This plan governs the first whole internal and computational bounded-free-
complex layer shared by Lambdapi, the native TypeScript CAS, the proof--CAS
bridge, and the existing CAP-like categorical engine:

```text
formal matrices and exact chain squares
  -> recursive bounded free-complex spine
  -> whole polynomial complexes and Schreyer conversion
  -> whole chain maps with every computed square
  -> typed operations and graphs
  -> explicit Core realization and classified adoption
  -> identity/composition and categorical compatibility
  -> portable artifacts and live backend conformance.
```

The goal stops before quotient-module semantics, complexes of presented
modules, kernels, cokernels, exactness, homology, or Čech cohomology. Direct
matrices remain the concrete backend beneath category/doctrine/tower/compiler
abstraction.

## Operational Baseline

The completed presentation-morphism branch was fast-forwarded to the
historical `main` worktree before this branch was created. `main` and this
branch share baseline `c9d8e5f`. Orthogonal path-cubical and strictness-
migration branches remain excluded.

The root and nested repository guidance remain mandatory. The user authorizes
local validated checkpoint commits on this dedicated branch. This does not
authorize push, merge, publication, release, PR creation, history rewriting,
branch deletion, worktree removal, or integration of orthogonal work.

## Why Bounded Free Complexes Come Next

The completed presentation-morphism goal supplies individual exact equations

```text
d_(i-1) o d_i = 0
e_i o F_i = F_(i-1) o d_i,
```

but does not package an arbitrary finite sequence as one internally typed
complex or chain map. The next goal should promote those local laws into a
whole recursive structure rather than accumulate disconnected square arrays.

Quotient semantics are not needed for complexes of finite free modules.
Homology would be premature because it requires selected module objects,
kernels, cokernels, and quotient semantics. Current Čech data are varying-ring
and semilinear rather than one fixed-ring complex. A bounded free complex is
therefore the direct dependency-ready continuation.

## Formal Recursive Complex Design

A flat `FiniteFamily` of matrices is not selected: adjacent matrices have
different source and target ranks, so a homogeneous family would erase the
typing relationship or require a second lookup/indexing layer.

Instead define a continuation above one already-selected boundary

```text
d : R^current -> R^below
```

by the recursive classifier

```text
ChainTail_R(0; below,current,d)
  = Unit

ChainTail_R(n+1; below,current,d)
  = Sigma nextRank,
      Sigma e : Matrix_R(current,nextRank),
        Chain0(d,e)
        x ChainTail_R(n; current,nextRank,e).
```

Here `Chain0(d,e)` is the existing exact classifier `d o e = 0`. A whole
complex separates the first differential, which has no preceding chain
condition:

```text
BoundedFreeComplex_R(0)
  = Nat

BoundedFreeComplex_R(n+1)
  = Sigma rank0,
      Sigma rank1,
        Sigma d1 : Matrix_R(rank0,rank1),
          ChainTail_R(n; rank0,rank1,d1).
```

The owner-position probe rejected the initially proposed dummy zero boundary:
`0 o d_1 = 0` is mathematically valid but not judgmental for an arbitrary
formal ring, because matrix action still exposes ring multiplication/addition
laws. Storing that redundant first law would require theorem-level matrix
algebra unrelated to the genuine chain conditions. The selected two-level
representation begins stored laws only with `d_1 o d_2 = 0`.

This representation:

- uses only existing Nat, Sigma/Product, matrix, and equality owners;
- internalizes every varying rank in the next Sigma binder;
- stores every chain law next to the differential that creates it;
- avoids `Fin`, lookup, arrays, lists, or heterogeneous casts; and
- remains one whole internal term.

Expose transparent nil/cons constructors and successor projections for next
rank, differential, chain law, and remaining tail. The whole complex exposes
degree-zero rank and tail. Start with semantic definitions. A stable projection
head is justified only if a focused consumer demonstrates conversion or
matching failure.

## Formal Recursive Chain-Map Design

For two length-`n` complex tails and a current component

```text
F_i : C_i -> D_i,
```

define recursively

```text
ChainMapTail(0; sourceTail,targetTail,F_i)
  = Unit

ChainMapTail(n+1; sourceTail,targetTail,F_i)
  = Sigma F_(i+1) : C_(i+1) -> D_(i+1),
      ChainSq(d_(i+1),e_(i+1);F_i,F_(i+1))
      x ChainMapTail(n; sourceRest,targetRest,F_(i+1)).
```

The local law is the existing

```text
e_(i+1) o F_(i+1) = F_i o d_(i+1).
```

A whole chain map retains the degree-zero component plus this recursive tail.
Components are the input data; squares are computed by the CAS and supplied to
the formal package after exact adoption. The end-user usability layer must not
accept independent hand-written square proofs.

### Projection feasibility gate

The formal owner audit must first probe the whole `ChainTail` classifier,
constructors, and projections. Only after those are stable should it define
`ChainMapTail`, whose motive depends on both source and target tail projections.

If transparent projections are conversion-heavy, the fallback is a narrow
stable schema/projection owner around the same recursive representation. The
fallback is not a flat array, a manual cone/square record, or a return to
unrelated equation assumptions. If separately packaged source/target tails
make the chain-map motive brittle, a jointly recursive aligned chain-map spine
may be selected, but it must retain projections to the same whole source and
target complex data and document the duplication boundary.

## Computational Representation

Implement a ring-generic polynomial bounded free complex:

```text
AlgebraPolynomialBoundedFreeComplex
```

retaining:

- one ordered term/free module in every consecutive degree;
- one ordered differential between adjacent degrees;
- every adjacent composite as a whole map;
- every zero/nonzero chain-condition result;
- minimum/maximum degree or the normalized zero-based bound;
- completeness/truncation metadata when sourced from a resolution; and
- the originating Schreyer resolution when applicable.

Endpoint/ring/rank mismatches are structural errors. A candidate with a
nonzero adjacent composite remains a whole negative result with its composite
matrix; it is not silently rejected before the proof--CAS layer can observe
the failure.

Implement

```text
AlgebraPolynomialBoundedChainMap
```

retaining:

- source and target complexes with one common degree range;
- one component in every degree;
- every computed chain square and both composite sides;
- the first/all noncommuting squares;
- identity and composition results; and
- exact status independent of a Boolean projection.

The existing field-linear `AlgebraModuleChainComplex` and
`AlgebraModuleChainMap` are comparison/reference implementations, not the
primary owner. The new layer is polynomial/free and aligns directly with the
formal commutative-ring matrix surface.

## First Consumers

### Schreyer resolution

Convert an existing `AlgebraPolynomialSchreyerResolution` into the generic
bounded-free-complex owner. The conversion must preserve free-module and
differential order, maximum length, truncation/completeness status, and every
adjacent-zero equation. Revalidation occurs through the new generic complex
constructor rather than trusting the source result by type alone.

### Chain maps

Construct at least:

- the identity chain map of the selected resolution;
- a nontrivial scalar/componentwise chain map;
- their composition; and
- a changed component producing a retained noncommuting square.

Identity and composition are revalidated through the same whole chain-map
constructor. Formal identity-matrix and category-law owners remain
consumer-gated; CAS-selected component matrices and adopted square equations
are sufficient for the first formal packages.

## Operations, Graphs, And Categorical Layer

Expose whole operations for:

- complex construction/validation;
- Schreyer-resolution conversion;
- chain-map construction/validation; and
- identity/composition where a separate operation is useful.

Each operation has exact structural schemas, deterministic serializers,
reference implementations, and graph execution. At least one retained complex
or chain-map program must agree byte-for-byte between direct execution and an
`AlgebraComputationGraph`.

The TypeScript category layer should treat complexes as objects and chain maps
as morphisms, with identity/composition using the whole validated owners. A
small category/tower/compiler consumer should lower to the direct polynomial
representation. Generic homology remains a later doctrine consumer and must
not depend directly on matrix internals.

A formal `Cat` of complexes is not required by this goal. The Lambdapi nucleus
still has no generic category-record constructor; introducing a category head
would require a separate complete owner/rule/projection design.

## Proof--CAS Bridge

Reuse the existing exact request/execution/workflow/adoption/assumption-source
owners. Reification must retain the whole recursive complex or chain map and
the exact selected matrices.

Positive complexes adopt every `d^2=0` law in recursive order before building
the formal tail. Positive chain maps adopt every component square in recursive
order before building the formal chain-map tail. Each law remains a separate
`computed-equation` assumption with its whole computation artifact.

Negative complexes or chain maps are observations and cannot construct the
law-bearing formal package. They retain the nonzero composite or unequal square
sides. Exact Core target, parent/rank/order identity, selected whole-output
bytes, and realization profile are mandatory adapter checks.

## CAP/homalg Architectural Contract

The selected layering remains:

```text
exact polynomial/matrix algorithms
  -> free modules, complexes, and chain maps
  -> typed whole operations and graphs
  -> direct computable category
  -> doctrine/tower/compiler consumers
  -> explicit formal realization and adoption.
```

This is the complex/chain-map analogue of the CAP/homalg separation between
matrix backends, concrete categories, and generic homological algorithms.
Emdash additionally retains exact Core goal and adoption identity. It does not
claim comparable package breadth, API compatibility, or proof of the CAS.

## Proposed Implementation Sequence

1. Probe formal `ChainTail`, nil/cons, projections, and first zero-boundary
   computation.
2. Promote the whole bounded-free-complex formal package and reviewer.
3. Probe and promote whole formal `ChainMapTail` and chain-map package.
4. Implement polynomial bounded-complex whole results and negative composites.
5. Convert Schreyer resolutions through the generic complex owner.
6. Implement polynomial chain maps, identity, composition, and negatives.
7. Expose operations, schemas, serializers, reference engines, and graphs.
8. Add exact Core recursive reification, classified law adoption, and package
   construction.
9. Add direct complex/chain-map category and compiler compatibility.
10. Register formal owners, update standing documentation, and pass focused
    live Lambdapi conformance.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `FBC-PLAN-0` | in progress | completed presentation morphisms at `c9d8e5f` and reviewed continuation | living plan, isolated branch/worktree, exact baseline, recursive design, validation, Git limits |
| `FBC-AUDIT-1A` | complete; checkpoint `1789918` | plan | owner-position `ChainTail` probe, projection/zero-boundary feasibility, exact fallback classification |
| `FBC-FORMAL-COMPLEX-2A` | complete; checkpoint `ccc0499` | audit | rule-minimal recursive formal complex, constructors/projections, positive/noncollapse reviewer |
| `FBC-FORMAL-MAP-3A` | complete; checkpoint `3a934c7` | formal complex | recursive formal chain map or documented aligned-spine fallback, exact component squares |
| `FBC-COMPUTE-4A` | complete; checkpoint `3a934c7` | formal orientation | whole polynomial complex and negative chain-condition results |
| `FBC-SCHREYER-5A` | complete; checkpoint `3a934c7` | computational complex | lossless/revalidated conversion from bounded Schreyer resolutions |
| `FBC-CHAIN-MAP-6A` | complete; checkpoint `3a934c7` | complex | whole chain maps, identity, composition, and retained noncommuting squares |
| `FBC-OPERATIONS-7A` | complete; operations/category checkpoint pending | computational owners | exact schemas, operations, serializers, reference engine, direct/graph byte agreement |
| `FBC-BRIDGE-8A` | pending | formal/computational owners | recursive Core reification, exact adapters, ordered classified adoption, package construction, deterministic artifact |
| `FBC-CATEGORY-9A` | complete; operations/category checkpoint pending | chain maps/operations | direct computable category plus representative tower/compiler lowering and agreement |
| `FBC-CONFORMANCE-10A` | pending | all active rows | registration, standing docs, affected checks/lint, live Lambdapi acceptance, proportional final audit |

Rows may be split, rejected, or deferred only with durable evidence and a
synchronized plan. Every completed row requires focused positive/negative
tests, proportional validation, and a local checkpoint.

## Initial Decisions

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-FBC-001` | accepted | A recursive dependent tail is the canonical whole formal representation; a homogeneous matrix array is not. |
| `D-FBC-002` | accepted | The tail is parameterized by its current boundary, so each successor internalizes the next rank, differential, zero-composite law, and rest. |
| `D-FBC-003` | rejected after owner probe | A dummy zero boundary would store the redundant law `0 o d_1 = 0`, which is not judgmental over an arbitrary formal ring and would force unrelated matrix-algebra proofs. |
| `D-FBC-004` | accepted | Chain-map squares are computed from components and stored after adoption; they are not independent usability inputs. |
| `D-FBC-005` | accepted | Transparent projections are tried first; a narrow stable schema head is allowed only after a measured conversion failure. |
| `D-FBC-006` | accepted | A jointly aligned chain-map spine is a documented fallback, not permission to abandon whole source/target structure. |
| `D-FBC-007` | accepted | Polynomial/free complexes are primary; field-linear quotient-aware homology remains comparison evidence. |
| `D-FBC-008` | accepted | Schreyer resolutions are the first genuine consumer and must be revalidated through the generic complex owner. |
| `D-FBC-009` | accepted | Whole negative complexes/maps retain nonzero composites or unequal square sides; Boolean status is derived. |
| `D-FBC-010` | accepted | Quotient modules, presented-module complexes, exactness, homology, and Čech cohomology remain later layers. |
| `D-FBC-011` | accepted | No formal category of complexes is required; TypeScript category/compiler compatibility is sufficient here. |
| `D-FBC-012` | accepted | Direct matrices remain the backend beneath category/doctrine/tower/compiler abstraction. |
| `D-FBC-013` | accepted | Local validated checkpoints are authorized; push, merge, publication, release, history rewriting, and cleanup are not. |
| `D-FBC-014` | accepted | Orthogonal path-cubical/strictness histories remain excluded. |
| `D-FBC-015` | accepted after owner probe | A zero-length complex is just its degree-zero rank; a positive-length complex stores `rank0`, `rank1`, `d1`, then a `ChainTail` whose first stored law is the genuine `d1 o d2 = 0`. |
| `D-FBC-016` | accepted after owner probe | The transparent `ChainTail` Nat eliminator, nil/cons constructors, successor rank/differential/law/rest projections, and positive-length complex package all pass quietly without a stable head, rewrite, or unifier. |
| `D-FBC-017` | accepted during formal promotion | Complex and chain-tail owners remain transparent in a downstream rule-free module; visible two-differential construction and all selected projections compute without a stable facade. |
| `D-FBC-018` | accepted after chain-map probe | `CommRingFreeChainMapTail` recurses over two independently packaged complex tails; the aligned-spine fallback is unnecessary. |
| `D-FBC-019` | accepted after chain-map probe | A positive-length whole chain map stores `F0`, `F1`, the first square, then a recursive tail starting at `F1`; zero length is exactly one matrix between the two degree-zero ranks. |
| `D-FBC-020` | accepted during computation | Polynomial complexes use zero-based consecutive terms and `d_i : C_i -> C_(i-1)`; endpoint/ring/count failures are structural, while nonzero adjacent composites remain whole negative results. |
| `D-FBC-021` | accepted during Schreyer conversion | Resolution free-module/differential order, maximum length, completeness, and the original whole resolution are retained, while every adjacent composite is recomputed through the generic complex owner. |
| `D-FBC-022` | accepted during chain maps | A whole chain map retains one component per degree and every computed square; its status also requires both endpoints to be valid complexes. |
| `D-FBC-023` | accepted during chain maps | Identity and composition are constructed componentwise and re-enter the common whole validator; no privileged Boolean-only path or manually supplied square exists. |
| `D-FBC-024` | accepted during operation exposure | Complex construction, Schreyer conversion, and chain-map validation are separate typed whole operations; serializers retain terms, maps, composites/squares, negative status, and Schreyer metadata. |
| `D-FBC-025` | accepted during graph validation | Direct and graph execution agree on the complete bytes of a deliberately invalid complex, proving that graph lowering does not project away the offending composite. |
| `D-FBC-026` | accepted during category compatibility | Polynomial complexes and validated chain maps form a direct computable category at the plain `Category` doctrine; one constructor/reinterpretation/compiler lowering targets the native chain-map operation without a formal category or homology claim. |

## Initial Formal Owner Audit Result

The owner-position probe implements `ChainTail` as a Nat eliminator returning
a dependent function of `below`, `current`, and the selected boundary matrix.
Its successor is the intended nested Sigma/Product of next rank,
differential, exact composite-zero law, and recursive rest. Transparent
nil/cons and all four successor projections elaborate and compute on a visible
two-differential consumer.

The first probe also tested the proposed uniform zero boundary. Although the
tail recursion itself and all projections checked, the conversion assertion
`0_(0,r0) o d1 = 0_(0,r1)` failed: the formal matrix evaluator does not erase
arbitrary ring multiplication/addition laws judgmentally. The design was
therefore corrected rather than patched with a rewrite or opaque theorem.

The revised whole complex is `Nat` at length zero and the nested package
`rank0, rank1, d1, ChainTail(n;rank0,rank1,d1)` at successor length. That
classifier, constructor, and rank/differential projections pass in the same
quiet probe. No stable schema fallback is currently needed for complexes;
chain-map recursion remains the next separate projection audit.

## Initial Formal Complex Result

`emdash2/emdash3_2_commutative_algebra_bounded_free_complexes.lp` promotes the
audited representation without a rule or unifier. `CommRingFreeChainTail`
owns the Nat recursion; nil/cons constructors and next-rank, differential,
law, and rest projections are transparent. `CommRingBoundedFreeComplex` is
`Nat` at length zero and the nested positive-length package selected by the
audit, with projections for both initial ranks, `d1`, and the recursive tail.

The independent reviewer constructs a visible two-differential complex from
one supplied genuine adjacent-zero law and exposes both ranks and both
differentials through the projection ladder. Distinct selected first
differentials remain runtime-distinct. Owner and reviewer pass quiet bounded
Lambdapi checking. The separate chain-map owner-position probe now also
confirms that recursion over two independently packaged tails and the whole
positive-length `F0/F1/first-square/rest` package elaborate without the
aligned-spine fallback.

## Initial Formal Chain-Map Result

`emdash2/emdash3_2_commutative_algebra_bounded_free_chain_maps.lp` promotes
the successful two-tail motive. At every tail successor it extracts the next
source/target ranks and differentials from the already-packaged complexes,
binds the next component, stores `CommRingChainMapSquare`, and recurses on both
rest projections. Nil/cons plus next-map, law, and rest projections are
transparent.

`CommRingBoundedFreeChainMap` is a single matrix at length zero. At positive
length it retains `F0`, `F1`, the first square over `d1/e1`, and the remaining
map tail beginning at `F1`. The reviewer constructs a one-differential map,
exposes both components, and confirms that distinct selected `F0` matrices
remain runtime-distinct. Owner and reviewer pass quiet bounded checking with
no stable head, rule, unifier, or duplicated source/target spine.

## Initial Computational Complex Result

`src/v3_2/algebra_polynomial_bounded_complex.ts` now owns zero-based bounded
free complexes and chain maps. A complex retains ordered free modules,
differentials, every adjacent composite, each zero status, its length, and an
overall status. Ring, count, and endpoint mismatches are rejected, but a
nonzero composite remains inspectable rather than causing construction to
discard the candidate.

Schreyer conversion preserves the source resolution, free modules,
differentials, maximum length, and completion status, while reconstructing all
conditions through the generic complex owner. The representative complete
length-two resolution remains a valid complex.

A chain map retains every component and square. Identity, scalar maps, and
composition return through the same constructor; a changed component produces
an `isChainMap = false` result with the unequal square sides retained. Focused
tests cover valid/invalid complexes, nonzero composite visibility, Schreyer
metadata, identity/scalar/composition, and a negative square. Eleven directly
affected polynomial presentation tests, root typecheck, and affected lint
pass.

## Operations, Graph, And Category Result

`src/v3_2/algebra_polynomial_bounded_complex_reference_operations.ts` exposes
whole complex construction, Schreyer conversion, and chain-map validation with
separate schemas and reference algorithms. Canonical serializers retain every
term rank/order, differential, adjacent composite, square side, status, and
Schreyer completion field. A deliberately invalid complex serializes
byte-for-byte identically through direct and graph execution.

`src/v3_2/algebra_polynomial_bounded_complex_category.ts` supplies the direct
computable category over one polynomial ring. Objects are bounded free
complexes; morphisms are whole chain maps; identity/composition reuse the
common validated owners. The model remains at doctrine `category`, records one
complex constructor and direct reinterpretation, and lowers chain-map
validation to the native graph operation. Focused tests confirm categorical
identity/composition, direct/compiled byte agreement, the selected primitive
method, and retained reinterpretation rule.

## Validation Policy

- Documentation-only changes receive exact diff, link, registry, and Markdown
  hygiene checks.
- TypeScript changes receive workspace validation, root typecheck, affected
  lint, and focused polynomial/complex/graph/category tests.
- Formal changes follow the complete nested Lambdapi SOP: owner-position
  probes, focused owner/reviewer checks, warning-location comparison, strict
  LHS audit if rules exist, registration, catalog/health synchronization, and
  live emitted-Core probes.
- Every Lambdapi target is bounded to at most 90 seconds.
- Preserve the integrated scoped-validation policy: avoid repository-wide
  TypeScript, formal, book, print, package, or release aggregates beyond an
  actually affected integration boundary.
- Carry recent green evidence for unchanged boundaries.

## Non-Goals

- quotient, setoid, HIT, action-groupoid, or Freyd semantics for modules;
- complexes of quotient/presented modules;
- kernels, cokernels, images, exactness, or homology;
- functorial or connecting homology maps;
- varying-ring semilinear complexes;
- Čech differentials or cohomology;
- an unbounded, cochain, bicomplex, DG, or spectral-sequence formalism;
- a forced formal category head for complexes;
- proof certificates or proof of the CAS;
- GAP/CAP API compatibility, parser, hosted service, or publication; or
- push, merge, release, PR creation, history rewriting, branch deletion, or
  worktree cleanup.

## Completion Boundary

The goal completes when every active ledger row is implemented,
audit-rejected, or explicitly deferred behind a concrete prerequisite; a
whole bounded complex and chain map exist at the formal and computational
layers; Schreyer conversion, identity/composition, and negative cases use
those owners; exact laws flow through recursive Core realization and
classified adoption; a direct category/compiler consumer agrees with graph
execution; portable artifacts and live Lambdapi conformance pass; standing
documentation and registries are synchronized; and every bounded tranche is
checkpointed.

## Later Continuation

After this goal, the intended sequence is:

```text
bounded free complexes and chain maps
  -> selected quotient/action-groupoid/Freyd semantics
  -> complexes of presented modules
  -> formal kernels and cokernels
  -> homology and functorial homology
  -> varying-ring Cech complexes
  -> Cech cohomology.
```

## Persistent `/goal` Launch Prompt

Work in `/home/user1/emdash1-formal-bounded-free-complexes-v1` on
`goal/formal-bounded-free-complexes-v3.2`. Implement the formal recursive
bounded-free-complex, whole polynomial complex/chain-map, Schreyer conversion,
proof--CAS delegation, categorical compatibility, and conformance objective
with every evolving recursive owner, projection/stability decision, fallback,
matrix orientation, whole result, reifier, adapter, trust classification,
artifact, validation result, checkpoint, and completion condition delegated
to this plan. Preserve baseline `c9d8e5f`, exclude orthogonal path-cubical and
strictness work, and re-read current source/SOP/plan on every continuation.
Treat direct matrices as the concrete backend beneath the CAP-like abstraction;
do not claim quotient modules, presented-module complexes, exactness, homology,
or a formal complex category. Add formal mathematics only under the nested
Lambdapi SOP, use proportional affected checks, make only local validated
checkpoint commits, and do not push, merge, publish, release, rewrite history,
remove worktrees, or broaden unrelated formal/kernel semantics.
