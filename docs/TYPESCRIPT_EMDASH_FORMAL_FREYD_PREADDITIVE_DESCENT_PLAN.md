# TypeScript/emdash Formal Freyd Preadditive Descent Plan

Date: 2026-09-01

Plan-ID: `TS-EMDASH-FORMAL-FREYD-PREADDITIVE-DESCENT`

Status: completed on a dedicated branch/worktree; implementation and
conformance checkpoint `c1b5a8e`

Baseline: `c7d1eb7d2a121b7bd27e36d14f344cc8070627fc`

Branch: `goal/formal-freyd-preadditive-descent-v3.2`

Worktree: `/home/user1/emdash1-formal-freyd-preadditive-v1`

Decision-Response-Evidence:

- `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a05c2d-08d4-7143-a5ff-690de2076edf`

## Purpose

This plan completes the formal algebraic layer deliberately left open by the
finite-free/Freyd presentation-category goal:

```text
selected finite-free matrix computation and theorem paths
  -> formal raw presentation identity/composition/zero/addition
  -> agreement compatibility for those operations
  -> groupoidified and 0-truncated quotient-Hom descent
  -> selected Freyd identity/composition/zero/addition classes
  -> preadditive Hom structure
  -> focused CAS/Core/Lambdapi conformance.
```

The formal Freyd category remains the primary module architecture. Direct
matrix algorithms remain the computational backend. Groupoidification and
truncation remain homwise quotient mechanisms rather than an independent
module foundation.

This goal does not claim biproducts, an additive-category package, weak
kernels, Abelian structure, kernels/cokernels, exactness, homology, presented-
module complexes, or Cech cohomology. Those require later capability-indexed
goals.

## Operational Baseline And Git Boundary

The branch starts at completed Freyd checkpoint `c7d1eb7`. Historical `main`
remains at `85f459a`; this goal does not fast-forward or otherwise mutate it.
Orthogonal path-cubical and global-strictness worktrees remain excluded.

The user authorized this dedicated branch/worktree and the established local
validated-checkpoint workflow for persistent goals. Checkpoints are permitted
only after a bounded tranche is green and this ledger is synchronized. This
does not authorize push, merge, publication, release, PR creation, amend,
rebase, reset, history rewriting, branch deletion, or worktree removal.

## Corrected Finite-Free Owner Audit

The completed plan's phrase “broad runtime identity/composition rules time
out” is too coarse. Focused warning-enabled probes establish the narrower
boundary:

| Candidate | Result | Consequence |
| --- | --- | --- |
| transparent recursive identity matrix | checks in about 5.6 seconds | identity recursion is not the problem |
| `id(Free_R,n) ->` transparent identity | checks in about 5.6 seconds | category-specific identity alone is feasible |
| `comp_Free(g,f) ->` rigid matrix-composition head | checks in about 5.6 seconds | generic `comp_fapp0` is not inherently too hot |
| `comp_Free(g,f) -> comm_ring_matrix_comp(g,f)` | exceeds 90 seconds | immediate transparent composition unfolding is unsuitable |
| replace all composition dimensions by `_` | fails type preservation | named plain dimensions are justified interface data |

The timeout comes from the overlap between the proposed transparent target and
the established strict functoriality cut

```text
F[g] o F[f] -> F[g o f].
```

The alternative path unfolds `comm_ring_matrix_comp` through `nat_elim`,
finite families, vectors, and the full commutative-ring record while local
confluence compares both branches. A runtime fold to a rigid head avoids that
explosion but reports twenty genuine higher-action overlaps. Warning count is
not a veto; those reports identify competing runtime normal forms whose joins
would need an explicit semantic owner and concrete consumer.

The promoted implementation therefore remains coherent:

```text
generic id and comp_fapp0       runtime owners
          =?                    proof-time unification
rigid finite-free matrix heads  projection-visible operations.
```

The reason is preservation of generic unit, associativity, functoriality, and
higher-action normalization—not preservation of a warning count. A later
runtime promotion remains possible if a concrete consumer requires it and the
unit/`fapp1`/`tapp*` overlaps receive measured joins.

The historical owner audit and standing descriptions must be corrected in the
first documentation tranche.

## Definitional, Proof-Time, And Propositional Boundaries

Three surfaces must remain distinct.

### Generic category composition versus the rigid matrix head

The active finite-free category has a proof-time comparison

```text
comp_fapp0(CommRingFiniteFree_cat(R),g,f)
  =?
comm_ring_finite_free_comp_matrix(R,g,f).
```

Both sides retain rigid heads. A typed equality whose body is `eq_refl` checks
because the `unif_rule` participates while elaborating the theorem. This is
the current usability bridge. It is not a runtime reduction.

### The rigid matrix head versus transparent matrix computation

`comm_ring_matrix_comp` is a transparent defined symbol. Its literal name is
not a lasting unification discriminator: Lambdapi unfolds it to its recursive
body while solving the comparison. Declaring a `unif_rule` with that readable
name and then immediately declaring an `eq_refl` path does not freeze or seal
the definition. The earlier rigid-to-transparent unifier did not solve.

The required bridge is therefore a constructed path, expected to use finite-
family induction/extensionality and the rigid head's column projections:

```text
comm_ring_finite_free_comp_matrix(R,g,f)
  =
comm_ring_matrix_comp(R,g,f).
```

It must not be postulated as an opaque equality. Changing the transparent
operation into an injective runtime owner would be a separate normal-form
migration with its own consumers, warning comparison, and downstream audit;
it is not presumed by this plan.

### Direct evaluator/CAS computation

The transparent matrix function and TypeScript matrix engine remain the
direct algorithmic surface. Formal category syntax need not reduce globally
to that body. The constructed comparison path is the bridge used by raw
presentation laws and conformance tests.

## Matrix Algebra Prerequisite

Build only the theorem-level matrix algebra consumed by presentations:

```text
I o A = A
A o I = A
(A o B) o C = A o (B o C)

(A+B) o C = A o C + B o C
A o (B+C) = A o B + A o C
0 o A = 0
A o 0 = 0.
```

The first owner probe must determine whether these are most robustly proved
for the transparent matrix functions and transported to the rigid categorical
heads, or proved columnwise for the rigid heads and compared afterward. Do not
install broad algebraic normalization rules merely to make the proofs
reflexive.

Required evidence includes:

- matrix/family extensionality at the actual column orientation;
- recursive identity and composition observations;
- scalar/vector addition, negation, and zero laws already available from the
  commutative-ring structure;
- positive nontrivial dimensions and zero-rank boundaries; and
- no collapse of arbitrary matrices or ring elements.

If a prerequisite law is absent from the current commutative-ring/finite-
family layer, add the smallest reusable theorem owner there rather than an
opaque presentation-specific witness.

## Formal Raw Presentation Operations

For a presentation

```text
P = [R_P : R^rP -> R^gP],
```

retain the existing relation-preserving raw morphism

```text
(F,W) : P -> Q
R_Q o W = F o R_P.
```

Construct in Lambdapi:

```text
id_P = (I_gP,I_rP)

(G,V) o (F,W)
  = (G o F,V o W)

0_(P,Q) = (0,0)

(F,W) + (G,V)
  = (F+G,W+V).
```

Their stored laws must be derived from the matrix theorem layer. TypeScript
already computes raw identity and composition; it is evidence and a
conformance oracle, not a substitute for these formal constructors.

## Agreement Algebra

For target-relation agreement

```text
F ~ G
  := Sigma H, R_Q o H = F-G,
```

construct the operations required for quotient descent:

- reflexivity using zero;
- symmetry using negation;
- transitivity using addition;
- compatibility with raw precomposition;
- compatibility with raw postcomposition;
- compatibility with zero and addition; and
- independence from the retained relation witness `W` of a raw morphism.

These are explicit internal paths over computed matrices. No manually entered
commuting-square record and no opaque equality bridge is selected.

The strongest reusable packaging should be selected only after probes. Likely
candidates are functors between fixed-endpoint agreement categories for unary
operations and a curried/binary operation for composition and addition.

## Groupoidification And Truncation Descent

For each `P,Q`, the active carrier remains

```text
RawHomGroupoid(P,Q) := Groupoidify(Agree(P,Q))
FreydHomSet(P,Q)    := Trunc_0(RawHomGroupoid(P,Q)).
```

Use existing `groupoidify_rec`/extension and `trunc_rec`/`trunc_map` owners.
Do not presume a new global `Groupoidify_func`. Binary operations may be
implemented by currying/repeated elimination or a narrowly justified product
adapter, depending on focused owner probes.

The class computations must expose:

```text
[id_raw(P)]                         : FreydHomSet(P,P)
[g] o [f] = [g o_raw f]             : FreydHomSet(P,S)
0 = [0_raw]                         : FreydHomSet(P,Q)
[f] + [g] = [f +_raw g]             : FreydHomSet(P,Q).
```

Representative independence must follow from the agreement operations, not
from comparison of raw `W` witnesses.

## Freyd Category Usability And Preadditivity

`CommRingFreydPresentation_cat(R)` already owns presentation objects and
quotient Homs. Generic category identity and composition remain runtime heads.
Selected rigid class operations should meet them through proof-time
unification only when two stable heads survive and a typed `eq_refl` theorem
validates the intended usability comparison.

If the class construction is transparent, do not assume its readable alias can
serve as a unification discriminator. Introduce a stable operation only when
its point/class observations or later higher action need to survive runtime
normalization, and relate it constructively to the transparent descent.

Package homwise zero and addition together with the checked distributivity
laws as the smallest formal preadditive structure needed by later Freyd
algorithms. There is presently no authoritative Lambdapi preadditive-category
record, so this tranche may need to introduce one after an owner inventory.
Do not call the result additive without finite biproduct data and laws.

## TypeScript And Formal-Bridge Alignment

Reuse the existing direct Freyd category rather than replacing it. Add only
the operations/adapters necessary to show that:

- direct raw identity/composition match the selected formal constructors;
- direct zero/addition match formal raw operations;
- computed congruence supplies the exact formal agreement premises; and
- class-level categorical programs preserve deterministic operation bytes.

The bridge remains usability/computation oriented. It does not require the CAS
to emit proof certificates for all internal algorithms.

## Proposed Implementation Sequence

1. Correct the prior owner-audit wording and record the warning-enabled probe
   matrix.
2. Inventory/probe finite-family extensionality and matrix identity,
   composition, zero, addition, and distributivity theorem owners.
3. Construct the rigid-to-transparent matrix-composition path and focused
   zero/rank-one consumers.
4. Construct formal raw presentation identity, composition, zero, and
   addition with their relation laws.
5. Construct agreement reflexive/symmetric/transitive and operation-
   compatibility maps.
6. Descend identity, composition, zero, and addition through
   groupoidification and `0`-truncation.
7. Connect the selected quotient-class operations to the generic Freyd
   category usability surface.
8. Introduce/package the smallest checked preadditive Hom structure.
9. Extend focused TypeScript/Core/Lambdapi conformance and deterministic
   artifacts only where the formal operations add a real consumer.
10. Register new formal owners/reviewers and synchronize the standing reports,
    catalog, health snapshot, and final ledger.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `FPD-PLAN-0` | complete; checkpoint `bcf807c` | completed Freyd checkpoint `c7d1eb7` | living plan, isolated branch/worktree, corrected owner model, baseline and Git limits |
| `FPD-OWNER-1A` | complete; checkpoint `8a053ae` | plan | durable correction of the transparent-composition timeout diagnosis and focused warning classification |
| `FPD-MATRIX-2A` | complete; checkpoint `75783e5` | owner audit | constructed rigid/transparent comparison plus required identity/associativity/zero/bilinearity paths |
| `FPD-RAW-3A` | complete; checkpoint `75783e5` | matrix theorem layer | formal raw presentation identity/composition/zero/addition with checked stored laws |
| `FPD-AGREE-4A` | complete; checkpoint `f41e8db` | raw calculus | reflexive/symmetric/transitive/additive and pre/postcomposition agreement operations |
| `FPD-DESCENT-5A` | complete; checkpoint `ad62202` | agreement operations | groupoidified and truncated identity/composition/zero/addition on quotient Homs |
| `FPD-FREYD-6A` | complete; checkpoint `ad62202` | quotient operations | selected class owners and usability comparisons for generic Freyd identity/composition |
| `FPD-PREADDITIVE-7A` | complete for hom operations and all raw-class laws; checkpoint `c1b5a8e`; arbitrary-quotient law promotion deferred behind proposition-valued groupoidification induction | class operations | honest class-preadditive capability; no full PreadditiveCategory, biproduct, or additive claim |
| `FPD-CONFORMANCE-8A` | complete; checkpoint `c1b5a8e` | active formal rows | focused direct/category/compiler/Core/Lambdapi agreement and artifacts |
| `FPD-CLOSE-9A` | complete; implementation checkpoint `c1b5a8e`, ledger finalized here | all accepted/deferred rows | registration, reviewers, standing docs, catalog/health, proportional final gates and checkpoints |

Rows may be split, rejected, or deferred only with durable evidence and a
synchronized ledger. A difficult proof is not by itself evidence that an
opaque axiom should replace it.

## Initial Decisions

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-FPD-001` | accepted | The earlier timeout diagnosis is narrowed to runtime reduction into transparent matrix composition. |
| `D-FPD-002` | accepted | Generic category identity/composition remain runtime owners pending a concrete joined runtime consumer. |
| `D-FPD-003` | accepted | Plain matrix-dimension variables remain on relevant rule/unifier surfaces when `_` fails type preservation. |
| `D-FPD-004` | accepted | A defined `comm_ring_matrix_comp` alias does not provide a lasting rigid unification head. |
| `D-FPD-005` | accepted | `eq_refl` validates the existing generic-to-rigid unifier, not a nonexistent rigid-to-transparent comparison. |
| `D-FPD-006` | accepted | The rigid-to-transparent bridge must be constructed or the normal-form architecture must be explicitly migrated; no opaque equality is allowed. |
| `D-FPD-007` | accepted | Warnings are diagnostic evidence, not a veto; the twenty rigid-runtime overlaps remain a consumer-gated join problem. |
| `D-FPD-008` | accepted | Formal raw operations precede quotient descent and preadditive packaging. |
| `D-FPD-009` | accepted | Preadditive does not imply additive; biproducts remain outside this bounded goal unless independently checked and explicitly admitted. |
| `D-FPD-010` | accepted | Weak kernels and the weak-kernel-to-Abelian theorem are the next goal after this descent, not part of it. |
| `D-FPD-011` | accepted | Existing TypeScript matrix/Freyd algorithms are reused as computations and conformance oracles. |
| `D-FPD-012` | accepted | Orthogonal path-cubical/global-strictness work is excluded. |
| `D-FPD-013` | accepted after owner proof | The rigid/transparent composition comparison is constructed by Nat recursion: zero columns are reflexive; successor heads agree definitionally and tails use the induction hypothesis through constant-family pathover. |
| `D-FPD-014` | accepted after owner proof | Generic finite-free composition reaches transparent evaluation propositionally by transitivity of the existing generic-to-rigid `eq_refl` usability path and the constructed rigid-to-transparent path. |
| `D-FPD-015` | accepted after law probe | Transparent matrix left/right identity and associativity are transported from generic category normalization through explicit named comparison paths; unification transitivity is not assumed. |
| `D-FPD-016` | accepted after raw-operation probe | A reusable matrix-square pasting path derives composite presentation laws by five explicit categorical steps; presentation identity/composition retain both generator and relation matrices. |
| `D-FPD-017` | accepted after additive-law probes | A rule-free derived ring-law layer and Nat-recursive vector/matrix layer construct additive-group laws, action linearity, zero composition, and both distributivity orientations. |
| `D-FPD-018` | accepted after raw-additive probe | Raw presentation zero and addition combine both stored matrices; their square laws are derived from matrix zero/bilinearity and the input square laws. |
| `D-FPD-019` | accepted after subtractive probe | Matrix inverse uniqueness derives involutive negation, negation/subtraction algebra, subtraction chaining, and preservation of subtraction by both composition arguments. |
| `D-FPD-020` | accepted after agreement probe | Target-factorization agreement is explicitly reflexive, symmetric, transitive, additive, and stable under arbitrary precomposition and relation-preserving postcomposition. |
| `D-FPD-021` | accepted after descent split | Direct runtime `fapp1_fapp0` for fixed raw agreement action times out even with a rigid RHS; the whole functor remains, while generic fapp1 meets a stable agreement-action head through a typed proof-time unifier. |
| `D-FPD-022` | accepted after warning audit | Outer groupoidification representations retain their constructed runtime fapp1 actions. Their six identity-action critical pairs are classified semantic overlaps, not a veto. |
| `D-FPD-023` | accepted after quotient probes | Whole agreement functors, representation transfors, and nested groupoidification/0-truncation recursion give composition and addition on arbitrary quotient Homs with raw-class computation. |
| `D-FPD-024` | accepted after usability probes | Generic Freyd identity/composition first meet rigid heads by proof-time unification; only after typed `eq_refl` validation do local rigid-head folds expose the raw identity class and descended composition. |
| `D-FPD-025` | accepted after alias probes | Direct unifiers to defined identity/composition or outer-action aliases do not fire here; sequential rigid intermediaries succeed. This confirms that immediate `eq_refl` is a test, not a consequence of declaration order. |
| `D-FPD-026` | accepted after inverse descent | Raw presentation negation, agreement under negation, and groupoidified/truncated negation complete the computational additive operations. |
| `D-FPD-027` | accepted at the law boundary | All additive-group and bilinear laws are checked on every generating raw class and packaged as class-preadditive evidence. Promoting them to arbitrary groupoidified/truncated points requires a generic dependent or proposition-valued groupoidification induction principle absent from the current API. |
| `D-FPD-028` | accepted during direct alignment | The direct polynomial Freyd model computes zero/add/negation and representative bilinearity while retaining the plain category doctrine and explicitly recording `formalLawBoundary = generating-raw-classes`. |
| `D-FPD-029` | accepted during live conformance | One live Core/Lambdapi probe checks both the original representative agreement and computed additive cancellation against the active class-preadditive formal module. |

## Current Matrix-Layer Result

`comm_ring_finite_free_comp_transparent_path` now constructs the previously
missing whole comparison without a rewrite, unifier, or opaque constant. Its
successor case reflects the actual nested-Sigma representation of a finite
column family. `comm_ring_finite_free_comp_fapp0_transparent_path` composes it
with the existing proof-time generic/rigid theorem. Explicit transports of the
rigid identity path and generic unit/associativity paths now prove transparent
matrix left/right identity and associativity. The owner passes quiet and
warning-enabled bounded checks, the focused reviewer consumes all paths, and
strict LHS audit remains empty. Zero and bilinearity remain the active part of
`FPD-MATRIX-2A`. The registered no-check health snapshot now contains 358
owner/reviewer files; no repository-wide timing claim is introduced.

`emdash3_2_commutative_algebra_presentation_operations.lp` now constructs raw
presentation identity and composition. Identity derives its square from the
two transparent matrix unit paths. Composition computes both matrix
components, while `comm_ring_matrix_square_comp_path` pastes the two stored
relation squares through transparent associativity. A focused reviewer checks
both projections, consumes the whole composite law, and retains a noncollapse
boundary. The additive continuation below supplies the remaining raw
operations.

The matrix prerequisite is now complete. A low-level derived ring-law module
supplies the missing opposite orientations and zero consequences of the
retained commutative-ring basis. The matrix additive-law module recursively
constructs finite-family extensionality, vector additive/scalar laws, matrix-
action linearity, matrix additive-group laws, zero composition, and left/right
distributivity. `emdash3_2_commutative_algebra_presentation_additive_operations.lp`
uses those paths to construct raw zero and addition together with their whole
relation squares. All three owners are rule-free, pass focused checks and
strict LHS audits, and have reviewer-facing positive/noncollapse consumers.

The agreement prerequisite is also complete. The subtractive matrix module
derives the inverse and subtraction algebra needed by target factorization.
`emdash3_2_commutative_algebra_presentation_agreement_operations.lp` exposes
the retained witness/law and constructs reflexivity, symmetry, transitivity,
addition, arbitrary generator-map precomposition, and postcomposition using
the outer raw map's relation witness. The owner and focused reviewer pass; no
runtime rule, quotient collapse, or opaque equality was added.

The quotient descent and category-usability rows are complete.
`emdash3_2_commutative_algebra_freyd_operations.lp` constructs fixed-operand
agreement functors, whole representation transfors, groupoidified binary
composition/addition, and their nested `0`-truncated operations. Both raw and
ordinary class betas compute. `emdash3_2_commutative_algebra_freyd_usability.lp`
then connects generic category identity/composition to those operations through
the validated sequential rigid-head pattern. The focused operations and
usability reviewers pass. Six outer identity-action overlaps are recorded;
the timed-out inner runtime action is kept proof-time instead.

Additive inverse now follows the same descent route. The formal class-law
module constructs additive unit, associativity, commutativity, inverse, and
both distributivity laws for every raw presentation class and packages zero,
addition, negation, and those theorems as explicit class-preadditive evidence.
This is intentionally not named a full `PreadditiveCategory` instance: the
current `Groupoidify` API exposes nondependent recursion and whole uniqueness,
but no generic proposition-valued dependent induction principle for extending
all class laws to arbitrary raw-groupoid and truncated points. That missing
generic principle is a concrete later prerequisite, not an opaque axiom filled
inside this goal.

The direct TypeScript model now mirrors the new computational operations.
Polynomial-module maps and presentation morphisms expose zero, addition, and
negation; the Freyd model publishes them as an additive Hom-operation
capability without promoting its doctrine. Focused tests check additive unit,
cancellation, and both distributivity orientations by target-factorization
congruence. Root typecheck, affected lint, nine direct/presentation tests, and
the live two-agreement Core/Lambdapi consumer pass. No root aggregate was run.

## Final Result

The completed branch supplies:

- the corrected finite-free composition-owner audit;
- a constructed rigid/transparent matrix-composition path;
- transparent matrix identity, associativity, zero, additive-group, and
  bilinearity paths;
- raw presentation identity/composition/zero/addition/negation with derived
  relation squares;
- reflexive, symmetric, transitive, additive, negative, precomposition, and
  postcomposition agreement operations;
- whole agreement functors and representation transfors;
- groupoidified and `0`-truncated composition, addition, and negation;
- sequential rigid-head usability paths for generic Freyd identity and
  composition;
- computational Hom-operation and class-preadditive evidence packages;
- direct TypeScript zero/add/negation and representative bilinearity; and
- live emitted-Core acceptance of representative and additive-cancellation
  agreement.

Every new formal owner and focused reviewer passes its bounded check. Strict
LHS audits are empty. Warning-enabled checking reports exactly six local
identity-action overlaps, all at the two deliberately retained outer
groupoidification fapp1 actions; the timed-out inner action remains proof-time.
Workspace validation, root typecheck, affected lint, nine focused direct/raw-
presentation tests, and the focused live conformance test pass. Catalog,
report, active-reference, source-TOC, and health checks are synchronized; the
health report is an honest no-check snapshot over 358 files. No repository-
wide TypeScript, Lambdapi, book, print, package, or release aggregate was run.

The one substantive deferred theorem is exact: the current nondependent
`Groupoidify` recursor does not provide the proposition-valued dependent
induction needed to promote every generating-class additive law to arbitrary
groupoidified and truncated points. No opaque witness or misleading full
`PreadditiveCategory` instance replaces it.

## Validation Policy

- Documentation-only tranches receive exact diff, report-index/header/link,
  active-reference, and Markdown hygiene checks.
- Every formal rule/unifier begins in a focused owning-position probe with a
  typed positive consumer and relevant negative/noncollapse consumer.
- Every unifier is exercised by typed `eq_refl`; conversion assertions alone
  are insufficient.
- Quiet checks are followed by warning-enabled checks when interactions are
  unclear. Warning differences are classified rather than used as numerical
  vetoes.
- Every promoted rule receives strict inferred-slot and subject-reduction
  audits; intentional explicit slots are documented only after `_`
  replacement probes.
- Each new owner and reviewer receives a bounded check of at most 90 seconds.
- TypeScript changes receive workspace validation, typecheck, affected lint,
  and focused tests. One full TypeScript aggregate is reserved for an actual
  shared integration boundary and is not presumed by this goal.
- Avoid repository-wide Lambdapi, TypeScript, package, print, book, and release
  aggregates when scoped evidence is sufficient.
- Catalog and health metadata are synchronized only after tracked owner/check
  changes stabilize.

## Non-Goals

- rewriting generic finite-free composition directly to the transparent
  recursive matrix body;
- sealing or making transparent matrix operations opaque merely to obtain an
  `eq_refl` proof;
- broad matrix ring normalization in the kernel;
- arbitrary quotient carriers as the primary module architecture;
- a full arbitrary-quotient `PreadditiveCategory` instance before generic
  proposition-valued groupoidification induction;
- finite biproducts or an additive-category claim;
- weak kernels or a weak-kernel-to-Abelian theorem;
- formal kernels, cokernels, images, coimages, exactness, or homology;
- presented-module or Cech complexes;
- complete CAP/homalg API compatibility;
- proof-certificate requirements for ordinary CAS delegation;
- integration of orthogonal strictness/cubical work; or
- push, merge, publication, release, PR creation, history rewriting, branch
  deletion, or worktree cleanup.

## Completion Boundary

The goal completes when every active row is implemented, rejected with durable
evidence, or deferred behind a concrete prerequisite; the prior timeout
diagnosis is corrected; a non-opaque formal matrix comparison/theorem layer
supports raw presentation identity/composition/zero/addition; agreement makes
those operations representative-independent; groupoidification and
`0`-truncation expose quotient-Hom operations; generic Freyd identity and
composition have a selected usability comparison with their raw classes;
homwise zero/addition/negation and raw-class distributivity are packaged as
honest class-preadditive evidence; full arbitrary-quotient laws are deferred
behind the named generic induction prerequisite; focused cross-layer
conformance passes; and every bounded tranche is recorded and checkpointed.

## Later Continuation

```text
proposition-valued/dependent Groupoidify induction
  -> full preadditive Freyd presentation category
  -> computable weak kernels of finite-free matrices
  -> constructive weak-kernel-to-Abelian promotion
  -> kernels, cokernels, images, coimages, and exactness
  -> complexes of presented modules and homology
  -> varying-ring Cech complexes and cohomology.
```

The local CAP/homalg/Freyd-category source checkouts remain algorithm and API
references for those later universal-construction layers. They are not needed
to replace the present formal matrix theorem prerequisite.

## Persistent `/goal` Launch Prompt

Work in `/home/user1/emdash1-formal-freyd-preadditive-v1` on
`goal/formal-freyd-preadditive-descent-v3.2`. Implement the formal raw-
presentation algebra and preadditive quotient-Hom descent described by this
plan, with every evolving matrix-law owner, rigid/transparent comparison,
category rule, unification rule, agreement operation, groupoidification/
truncation adapter, reifier, CAS operation, warning classification, artifact,
validation result, checkpoint, and completion condition delegated to this
living plan. Preserve baseline `c7d1eb7`, exclude orthogonal path-cubical and
global-strictness work, and re-read current source/SOP/plan on every
continuation. Do not assume that a transparent defined symbol remains a rigid
unification head; validate every unifier with typed `eq_refl`; construct rather
than postulate the rigid-to-transparent matrix path. Do not claim biproducts,
an additive category, weak kernels, Abelian structure, kernels/cokernels,
exactness, homology, or Cech cohomology. Follow the nested Lambdapi SOP, use
proportional affected checks, make only local validated checkpoint commits,
and do not push, merge, publish, release, rewrite history, remove worktrees, or
broaden unrelated formal/kernel semantics.
