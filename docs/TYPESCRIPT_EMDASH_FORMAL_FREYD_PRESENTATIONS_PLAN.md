# TypeScript/emdash Formal Finite-Free And Freyd Presentation Categories Plan

Date: 2026-09-01

Plan-ID: `TS-EMDASH-FORMAL-FREYD-PRESENTATIONS`

Status: completed on a dedicated branch/worktree; implementation and
conformance checkpoint `320c8b8`.

Baseline: `85f459a5e6f7f20c4451c34ad14c5b0616090c12`

Branch: `goal/formal-freyd-presentations-v3.2`

Worktree: `/home/user1/emdash1-formal-freyd-presentations-v1`

Decision-Response-Evidence:

- `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a05bc6-0872-7b93-8dd2-5f567abb16e7`
- `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a05bd2-7050-7e23-875a-2e51d40caeee`

## Purpose

This plan promotes the existing finite matrices, presentations, morphism
witnesses, congruence, bounded complexes, and CAP-like TypeScript tower into
the primary formal categorical architecture:

```text
finite-free additive matrix category
  -> raw presentation objects and morphisms
  -> homwise morphism-agreement action categories
  -> groupoidified and 0-truncated quotient Homs
  -> Freyd/presentation category
  -> representable element semantics Hom(R,-)
  -> computational category/tower/compiler agreement
  -> capability boundary for later Abelian structure.
```

The Freyd/presentation category is the canonical long-term module
representation. Element action groupoids and set quotients are derived
realizations, not a parallel module foundation. The goal stops before
unconditional Abelian structure, kernels, cokernels, exactness, homology,
presented-module complexes, or Čech cohomology.

## Operational Baseline

The completed bounded-free-complex branch was fast-forwarded to the historical
`main` worktree before this branch was created. `main` and this branch share
baseline `85f459a`. Orthogonal path-cubical and strictness-migration branches
remain excluded.

The root and nested repository guidance remain mandatory. Local validated
checkpoint commits are authorized on this branch. This does not authorize
push, merge, publication, release, PR creation, history rewriting, branch
deletion, worktree removal, or orthogonal integration.

## Long-Term Architectural Decision

Direct quotient carriers are not the primary category of modules. The
category of finite presentations and morphisms modulo target-relation
congruence is primary because:

- objects and morphisms retain the exact matrices consumed by the CAS;
- composition, addition, kernels/cokernels, complexes, and homology are
  categorical operations over presentations;
- generic algorithms can depend on doctrines and roles rather than quotient
  carrier internals;
- element semantics can be derived representably; and
- the design matches the successful CAP/homalg layering of categories of
  rows/columns, Freyd categories, presentations, and derived algorithms.

Groupoidification and truncation remain essential, but they construct the
quotient Hom objects inside the Freyd category and the derived element
carrier. They do not compete with the categorical architecture.

## Formal Finite-Free Additive Category

Use the existing column orientation:

```text
Obj(Free_R) = Nat

Hom_Free_R(n,m)
  = Path_cat(Matrix_R(m,n))

id_n = I_n
g o f = matrix composition.
```

The formal prerequisite layer must add and prove only the matrix algebra
required by this category:

```text
I o A = A
A o I = A
(A o B) o C = A o (B o C)

(A+B) o C = A o C + B o C
A o (B+C) = A o B + A o C
0 o A = 0
A o 0 = 0.
```

Matrix identity should be a transparent finite-family construction. Laws are
theorem-level paths derived from ring and finite-family recursion, not broad
runtime rewrites. The category head may use selected `Obj`, `Hom`, identity,
and composition rules after owner-position probes, but the mathematical laws
must remain independently checkable.

Finite rank addition and block matrices are the eventual biproduct structure.
The first goal may package the category at the preadditive/additive capability
supported by checked operations; it must not claim missing biproduct laws.

## Raw Presentation Morphisms

A presentation is the existing matrix

```text
P = [R_P : R^r_P -> R^g_P].
```

A raw morphism is the completed data

```text
F : R^g_P -> R^g_Q
W : R^r_P -> R^r_Q
R_Q o W = F o R_P.
```

Identity and composition must retain both generator and relation matrices:

```text
id_P = (I_gP,I_rP)

(G,V) o (F,W)
  = (G o F,V o W).
```

The square law for composition follows from matrix associativity and both
stored laws. Different valid `W` witnesses for one `F` are representation data,
not distinct induced module maps.

Representative congruence is the completed target factorization

```text
F ~ G
  := Sigma H : Matrix_R(r_Q,g_P),
       R_Q o H = F-G.
```

It must be proved reflexive, symmetric, transitive, additive, and compatible
with pre- and postcomposition. These proofs are ordinary paths over explicit
matrices; no variable-headed rewrite or opaque equality bridge is selected.

## Homwise Agreement Action Categories

For fixed `P,Q`, define a category whose objects are raw presentation
morphisms and whose arrows are representative-agreement witnesses:

```text
Obj(Agree(P,Q)) = RawPresentationMorphism(P,Q)

Hom_Agree(P,Q)(f,g)
  = Path_cat(PresentationMorphismAgreement(P,Q,F_f,F_g)).
```

Identity uses the zero `H`. Composition adds agreement matrices. Its equation
is derived from linearity and cancellation, not accepted as a manually
authored commutative square. This category retains different `H` choices and
their syzygies.

The category head is a genuine new semantic owner and will probably require
selected `Obj`, `Hom`, identity, and composition rules. Warning families are
diagnostic evidence, not an automatic veto. Every rule follows the inferred-
slot SOP and receives positive, negative, subject-reduction, and warning
audits.

## Quotient Homs By Groupoidification And Truncation

Use the active generic categorical HIT rather than inventing a bespoke
quotient syntax:

```text
RawHomGroupoid(P,Q)
  := Groupoidify(Agree(P,Q))

FreydHomSet(P,Q)
  := Trunc_grpd trunc_zero (RawHomGroupoid(P,Q)).
```

The groupoidification unit turns every agreement witness into a path between
raw representatives. The `0`-truncation makes equality proposition-valued for
the ordinary category while retaining the untruncated groupoid as a higher
semantic view.

The selected class map is

```text
raw morphism
  -> object of Groupoidify(Agree(P,Q))
  -> point of FreydHomSet(P,Q).
```

Composition and addition must descend through the groupoidification and
truncation recursors. Whole beta/eta/universality should reuse the active
groupoidification and truncation owners. A new generic source-functorial
`Groupoidify_func` is not presumed.

## Freyd Presentation Category

Define the category

```text
CommRingFreydPresentation_cat(R) : Cat
```

with

```text
Obj = CommRingPresentation(R)

Hom(P,Q) = Path_cat(FreydHomSet(P,Q)).
```

Identity is the class of the raw identity presentation map. Composition is the
descended class of raw composition. The category unit and associativity laws
should follow from raw matrix laws plus quotient recursion; do not add broad
representative-level collapse rules.

Hom addition and zero descend similarly, making the selected structure
preadditive. Additive/biproduct structure is promoted only when finite-free
rank sums, presentation sums, injections/projections, and their equations are
checked.

This category is the formal presentation/Freyd layer. It is not defined as a
category of quotient carriers and arbitrary functions.

## Representable Element Semantics

Let `FreeOne_R` be the rank-one presentation with no relations. Define the
ordinary element carrier of `P` representably:

```text
El(P) := FreydHomSet(FreeOne_R,P).
```

A raw map `FreeOne_R -> P` is exactly a vector in `R^g_P`; the congruence
condition is exactly

```text
Sigma c, R_P*c = v-w.
```

Thus the earlier element action groupoid is the source-`FreeOne_R`
specialization of the generic Hom-agreement groupoid. The goal should expose a
whole comparison between this representable carrier and the direct
vector/agreement reading, not create a second independent module notion.

Positive polynomial-module membership then yields:

```text
coefficients and A*c=v-w
  -> agreement arrow
  -> groupoidification path
  -> equality in El(P).
```

Negative membership retains its nonzero remainder and leaves equality open.

## Presentation-Map Descent

The Freyd category already contains presentation maps as morphisms, so
functorial action on representable elements comes from categorical
composition. The completed `F,W` data may also define the corresponding action
functor on the untruncated agreement groupoids for a higher comparison.

The primary equality is categorical composition in
`CommRingFreydPresentation_cat(R)`. Any direct vector map or quotient-carrier
function is a realization of that owner, not another semantic source.

## Capability-Indexed Abelian Boundary

Freyd categories supply formal cokernel completion of an additive category,
but Abelian structure is not unconditional. The constructive criterion is a
weak-kernel capability on the additive base.

Record a future capability such as

```text
HasComputableWeakKernels(Free_R)
```

or an equivalent coherent/syzygy interface. The later Abelian goal should
derive

```text
HasComputableWeakKernels(Free_R)
  -> IsAbelianCategory(Freyd_R).
```

No such evidence follows merely from `R : CommRing`. Supported polynomial
rings over operational fields may later construct it from the existing
Gröbner/syzygy algorithms. This goal records and tests the boundary but does
not claim kernels, cokernels, exactness, or homology.

## Computational TypeScript Architecture

Reuse and consolidate the current direct representations:

- ranks and polynomial free modules for finite-free objects;
- `AlgebraPolynomialModuleMap` for free morphisms;
- `AlgebraPresentedPolynomialModule` or the compatible presented-algebra
  module data for objects;
- whole relation-witness results for raw morphisms;
- whole representative-agreement results for congruence; and
- the existing category/doctrine/tower/compiler infrastructure.

Implement a direct Freyd presentation category whose morphism equality is the
computed congruence, not raw matrix equality. Identity/composition/addition
must preserve whole witnesses and revalidate. Exact schemas, whole operations,
graphs, serializers, and category compiler lowering remain mandatory.

The TypeScript canonical normal-form presented-module category is a concrete
realization/comparison. The formal Freyd category and direct computational
category should agree structurally without forcing runtime wrapper objects.

## Proof--CAS Bridge

Reuse the exact workflow and assumption-source infrastructure. Required
consumers include:

- matrix identity/associativity/linearity laws used by raw composition;
- positive/negative congruence computations;
- membership-to-representable-element equality;
- raw identity/composition class formation; and
- direct/category/graph agreement.

Successful CAS outputs retain selected matrices and coefficients and target
only exact formal laws. Negative outputs remain observations. The bridge must
not postulate a whole quotient equality, Freyd category, or Abelian doctrine as
one opaque assumption.

## Proposed Implementation Sequence

1. Audit/probe matrix identity, associativity, zero, and bilinearity theorem
   owners over finite families.
2. Implement the formal finite-free matrix category and TypeScript counterpart.
3. Implement raw presentation identity/composition and congruence algebra.
4. Implement fixed-endpoint agreement categories with selected rules.
5. Groupoidify and `0`-truncate agreement categories to quotient Hom sets.
6. Descend identity, composition, zero, and addition to define the Freyd
   presentation category.
7. Derive representable elements `Hom(FreeOne_R,-)` and compare with direct
   vector agreement/membership.
8. Add TypeScript operations, direct category, tower/compiler, graph, and
   deterministic artifacts.
9. Record/probe the weak-kernel/coherence capability boundary for the later
   Abelian goal.
10. Register formal owners, update standing documentation, and pass focused
    live Lambdapi conformance.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `FRP-PLAN-0` | complete; checkpoint `86c84d5` | completed bounded complexes at `85f459a` and reviewed categorical continuation | living plan, isolated branch/worktree, exact baseline, layered architecture, validation, Git limits |
| `FRP-AUDIT-1A` | complete; checkpoint `b4973c6` | plan | matrix-law and category-head owner probes, quotient-Hom orientation, capability boundary |
| `FRP-FREE-2A` | complete with stable-pointwise boundary; checkpoint `b4973c6` | audit | matrix identity/laws and formal/direct finite-free category |
| `FRP-RAW-3A` | complete computationally; explicit formal class descent deferred | finite-free category | raw presentation identity/composition/addition and congruence compatibility |
| `FRP-AGREE-4A` | complete with generic category operations; checkpoint `b4973c6` | raw morphisms | fixed-endpoint morphism-agreement categories with derived identity/composition |
| `FRP-QUOTIENT-HOM-5A` | complete; checkpoint `b4973c6` | agreement category | groupoidified and `0`-truncated quotient Hom objects and class maps |
| `FRP-FREYD-6A` | complete as category/Hom skeleton; explicit raw-class identity/composition descent deferred | quotient Homs | formal Freyd presentation category with descended identity/composition and selected preadditivity |
| `FRP-ELEMENTS-7A` | complete for raw-class agreement and direct representable comparison; checkpoint `b4973c6` | Freyd category | representable element carrier, membership-to-equality bridge, direct comparison |
| `FRP-COMPUTE-8A` | complete; checkpoint `b4973c6` | raw/congruence owners | whole operations, direct category, compiler/graph agreement, deterministic artifact |
| `FRP-ABELIAN-GATE-9A` | complete as explicit non-Abelian capability boundary; checkpoint `b4973c6` | Freyd category | explicit weak-kernel/coherence interface and supported-polynomial feasibility probe; no unconditional Abelian claim |
| `FRP-CONFORMANCE-10A` | complete; checkpoint `320c8b8` | all active rows | registration, standing docs, affected checks/lint, live Lambdapi acceptance, proportional final audit |

Rows may be split, rejected, or deferred only with durable evidence and a
synchronized plan. Every completed row requires focused positive/negative
tests, proportional validation, and a local checkpoint.

## Initial Decisions

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-FRP-001` | accepted | The Freyd/presentation category is the primary long-term module architecture. |
| `D-FRP-002` | accepted | Action groupoids and truncation construct quotient Homs and representable elements; they are not a competing module foundation. |
| `D-FRP-003` | accepted | The column-oriented finite-free category has Nat objects and `m x n` matrices as arrows `n -> m`. |
| `D-FRP-004` | accepted | Matrix category laws are theorem-level paths; broad normalization rewrites are not presumed. |
| `D-FRP-005` | accepted | Raw morphisms retain both `F` and `W`; quotient equality depends on `F-G` factoring through the target relation matrix. |
| `D-FRP-006` | accepted | Hom quotienting is performed by groupoidifying the agreement category and then applying `0`-truncation. |
| `D-FRP-007` | accepted | Ordinary elements are derived as `Hom(FreeOne_R,P)`. |
| `D-FRP-008` | accepted | No new independent quotient-carrier module notion is selected. |
| `D-FRP-009` | accepted | Abelian structure is capability-indexed by weak kernels/coherence; it is not global for arbitrary `CommRing`. |
| `D-FRP-010` | accepted | Existing polynomial Gröbner/syzygy algorithms are candidate constructors of later supported capability evidence. |
| `D-FRP-011` | accepted | Category-head warning families are measured and classified; warnings alone are not a veto. |
| `D-FRP-012` | accepted | No manually authored square/coherence fields enter the usability layer; all witnesses are computed or internally derived. |
| `D-FRP-013` | accepted | Direct matrices remain the backend beneath category/doctrine/tower/compiler abstraction. |
| `D-FRP-014` | accepted | Local validated checkpoints are authorized; push, merge, publication, release, history rewriting, and cleanup are not. |
| `D-FRP-015` | accepted | Orthogonal path-cubical/strictness histories remain excluded. |
| `D-FRP-016` | accepted after category probe | Broad runtime identity/composition rules on the finite-free category time out; generic category operations remain runtime owners and meet rigid pointwise matrix heads through proof-time unifiers. |
| `D-FRP-017` | accepted after category probe | Rigid identity/composition heads expose constructor-level Sigma projections; no unsupported whole equality with the older transparent matrix implementation is fabricated. |
| `D-FRP-018` | accepted after quotient-Hom probe | Agreement categories may keep generic identity/composition opaque while their objects/Homs feed `Groupoidify`; every explicit agreement witness still becomes a path and then a `0`-truncated equality. |
| `D-FRP-019` | accepted after Freyd probe | `CommRingFreydPresentation_cat` has presentation objects and quotient Hom sets, but explicit comparison of its generic identity/composition with classes of selected raw morphisms remains a separately gated construction. |
| `D-FRP-020` | accepted during computation | The direct TypeScript Freyd category uses computed target-factorization congruence as morphism equality; raw identity/composition revalidate through whole relation-witness computation. |
| `D-FRP-021` | accepted during representable comparison | A Freyd element is a raw morphism from the relation-free rank-one presentation; element equality is exactly presentation-morphism congruence and matches module membership in focused examples. |
| `D-FRP-022` | accepted at the Abelian gate | Polynomial rings with operational field coefficients expose a Gröbner/syzygy weak-kernel capability record whose `claimsAbelianStructure` field is false; the later theorem/instance remains separate. |
| `D-FRP-023` | accepted during conformance | Both formal owners and reviewers are registered; focused warning checks report zero local diagnostics after inferred-pattern cleanup. |
| `D-FRP-024` | accepted during live conformance | A CAS-computed representative-agreement Core law checks against the active Freyd module and is exactly the premise consumed by the formal groupoidification/truncation path. |
| `D-FRP-025` | accepted during conformance | Health is synchronized as an honest no-check 340-target snapshot under the established scoped-validation policy. |

## Owner Audit And Selected Formal Boundary

The matrix identity construction itself checks quickly. A first candidate that
rewrote generic finite-free category identity and composition directly to
transparent matrices timed out. Splitting the probe showed the recursive
identity was not responsible; the hot category rules were. The promoted design
therefore follows `CommRing_cat`: `Obj` and `Hom` compute, generic category
operations remain runtime owners, and rigid pointwise matrix heads meet them
at proof time. Narrow `sigma_Fst`/`sigma_Snd` rules expose identity and
composition columns. A body-unfolded unifier from the rigid composition head
to the older transparent matrix implementation did not solve the whole
comparison, so no such equality is claimed.

`CommRingPresentationAgreement_cat(R,P,Q)` computes objects to raw
relation-preserving morphisms and Homs to paths of target-factorization
agreement. Applying existing category-indexed `Groupoidify` and then
`Trunc_grpd trunc_zero` constructs a higher raw Hom groupoid and an ordinary
set-valued quotient Hom. The unit maps raw morphisms to classes; any explicit
agreement `H` maps to a path before and after truncation.

`CommRingFreydPresentation_cat(R)` computes objects to presentations and Homs
to path categories of those quotient sets. `FreeOne_R` yields the representable
element carrier. Generic Freyd identity/composition exist by the category head,
but their equality with classes of selected raw identity/composition matrices
is not yet implemented; selected preadditivity is consequently deferred with
that class-level descent rather than postulated.

## Direct Computational Freyd Result

`src/v3_2/algebra_polynomial_freyd_category.ts` supplies the concrete model.
Raw identity and composition compute generator maps and re-enter the whole
relation-witness constructor. Morphism equality recomputes target-relation
agreement rather than comparing raw matrices or `W` witnesses. The category,
one constructor/tower, direct reinterpretation, operation lowering, and graph
engine use these owners.

The rank-one relation-free presentation represents elements. A vector becomes
a raw map from that presentation; congruence between such maps is exactly
membership of the vector difference in the target relations. Focused tests
show `x=0` in the presentation by `(x)` while `y!=0`, validate categorical
identity/composition, and obtain byte-identical direct/compiled raw-morphism
results.

The supported-polynomial weak-kernel record requires operational field
coefficients and identifies the Gröbner/syzygy basis, but explicitly records no
Abelian claim. It is readiness data for the next capability-indexed theorem,
not an instance of it.

## Conformance Result

The finite-free and Freyd-presentation owners and both reviewers are
registered. Quiet focused checks pass. Warning-enabled checking reports no
diagnostic located in either new module after reconstructible variables were
replaced by `_`; strict LHS audits are clean.

Formal reviewers check the finite-free object/Hom surface, rigid identity and
composition column observations, agreement category, groupoidified and
`0`-truncated Hom objects, explicit agreement paths, Freyd category Hom
surface, and representable elements. Live emitted-Core checking accepts a
CAS-computed target-factorization law against the active Freyd module; that
law is the exact input to the checked quotient-path constructor.

Standing current-status, Foundations, canonical-syntax, report-index, and
health documentation records the primary categorical architecture and all
nonclaims. The strict catalog is synchronized. Health records 340 maintained
owner/reviewer files as an honest no-check source snapshot; no repository-wide
timing or aggregate claim is introduced.

The next formal dependency remains explicit: construct class-level identity,
composition, zero, and addition on quotient Homs, then promote preadditivity;
only afterward should the weak-kernel capability feed a constructive
weak-kernel-to-Abelian theorem.

## Validation Policy

- Documentation-only changes receive exact diff, link, registry, and Markdown
  hygiene checks.
- TypeScript changes receive workspace validation, root typecheck, affected
  lint, and focused matrix/presentation/category/graph tests.
- Formal changes follow the complete nested Lambdapi SOP: owner-position
  probes, positive/noncollapse consumers, warning and subject-reduction
  comparison, strict inferred-slot audit, registration, catalog/health
  synchronization, and live emitted-Core probes.
- Every Lambdapi target is bounded to at most 90 seconds.
- Preserve scoped validation: avoid repository-wide TypeScript, formal, book,
  print, package, or release aggregates outside an affected integration
  boundary.
- Carry recent green evidence for unchanged boundaries.

## Non-Goals

- unconditional Abelian structure for arbitrary `CommRing`;
- formal kernels, cokernels, images, coimages, or exactness;
- complexes of presented modules or homology;
- varying-ring semilinear Freyd categories;
- Čech differentials or cohomology;
- a second independent quotient-element type;
- proof of the CAS or certificate-centered integration;
- GAP/CAP API compatibility, parser, hosted service, or publication; or
- push, merge, release, PR creation, history rewriting, branch deletion, or
  worktree cleanup.

## Completion Boundary

The goal completes when every active row is implemented, audit-rejected, or
explicitly deferred behind a concrete prerequisite; finite-free and Freyd
presentation categories exist at the selected formal and direct computational
layers; quotient Homs are constructed by agreement-groupoid completion and
`0`-truncation; representable elements consume actual membership coefficients;
raw/category/graph computations agree; the weak-kernel Abelian boundary is
explicit; portable artifacts and live conformance pass; standing documentation
and registries are synchronized; and every bounded tranche is checkpointed.

## Later Continuation

```text
finite-free and Freyd presentation categories
  -> explicit quotient-class identity/composition and preadditivity
  -> computable weak-kernel/coherence capability
  -> capability-indexed Abelian structure
  -> complexes of presented modules
  -> formal kernels, cokernels, and homology
  -> varying-ring Cech complexes and cohomology.
```

## Persistent `/goal` Launch Prompt

Work in `/home/user1/emdash1-formal-freyd-presentations-v1` on
`goal/formal-freyd-presentations-v3.2`. Implement the formal finite-free
additive matrix category, raw presentation calculus, homwise agreement
groupoid/truncation quotient, Freyd presentation category, representable
element semantics, TypeScript category/compiler alignment, and Abelian
capability boundary with every evolving matrix-law owner, category rule,
quotient orientation, groupoidification/truncation adapter, reifier, CAS
operation, warning classification, artifact, validation result, checkpoint,
and completion condition delegated to this plan. Preserve baseline `85f459a`,
exclude orthogonal path-cubical/strictness work, and re-read current
source/SOP/plan on every continuation. Treat the Freyd category as primary and
action quotients as homwise/representable constructions; do not claim
unconditional Abelian structure, kernels/cokernels, presented-module
complexes, homology, or Čech cohomology. Follow the nested Lambdapi SOP, use
proportional affected checks, make only local validated checkpoint commits,
and do not push, merge, publish, release, rewrite history, remove worktrees, or
broaden unrelated formal/kernel semantics.
