# TypeScript/emdash Constructive Freyd Pre-Abelian Computation Plan

Date: 2026-09-01

Plan-ID: `TS-EMDASH-FREYD-PREABELIAN-COMPUTATION`

Status: active on a dedicated branch/worktree

Baseline: `c781a42972a3e91f60a79bfd95989ca4dca4aaac`

Branch: `goal/freyd-preabelian-computation-v3.2`

Worktree: `/home/user1/emdash1-freyd-preabelian-v1`

Decision-Response-Evidence:

- `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a05e5a-2c22-7450-9548-5d306f1a4a1c`

## Purpose

This plan is the immediate constructive successor to the completed
computational weak-kernel development. It consumes selected weak kernels in
an additive base category to compute genuine kernels and cokernels in its
Freyd category, exposes complete universal-construction operations through
the backend-neutral TypeScript category/CAS engine, and adds the corresponding
internal Lambdapi universal-property layer.

The intended bounded theorem boundary is **computational pre-Abelian
structure**, not merely a doctrine label and not yet the full Abelian theorem:

```text
additive base category P
  + computational weak kernels in P
  -> computational weak pullbacks in P
  -> unconditional cokernels in A(P)
  -> kernels in A(P)
  -> computational pre-Abelian structure on A(P).
```

This division follows the constructive proof architecture in Sebastian
Posur's *A constructive approach to Freyd categories*. Construction 3.6 gives
cokernels in every Freyd category. Weak kernels yield weak pullbacks, and
Construction 3.10 uses them to construct kernels. Constructions 3.13 and 3.14
then supply lifts along monomorphisms and colifts along epimorphisms; those
later constructions finish the Abelian theorem and are deliberately reserved
for the successor goal.

The goal therefore makes the first operational passage from CAP/homalg-style
base algorithms to actual universal constructions in the presented/Freyd
category. The polynomial matrix provider remains the first executable
instance, while interfaces and formal universal properties remain generic.

## Operational And Git Boundary

The branch starts from completed weak-kernel checkpoint `c781a42`. Before the
branch was created, the clean historical `main` worktree was fast-forwarded
from `85f459a3` to `c781a42`; the ancestry had zero divergent `main` commits.
No path-cubical, global-strictness, or other orthogonal branch was merged.

The baseline already contains:

- a formal Freyd presentation category with quotient Hom sets, selected
  identity/composition usability, preadditivity, finite direct sums, binary
  products, terminal zero, Cartesian structure, and `AdditiveCategory`;
- a backend-neutral polynomial Freyd category with genuine additive
  operations, compiler lowerings, and reference execution;
- complete original-column polynomial syzygies;
- computational weak-kernel objects, arrows, selected nonunique factors, and
  checked annihilation/reconstruction;
- a qualified additive finite-free polynomial weak-kernel provider;
- an internal Hom-fibre `ComputationalWeakKernel` and
  `HasComputationalWeakKernels` interface; and
- selected proof-CAS equation reification plus a non-authoritative Singular
  differential oracle.

The user explicitly authorized this new living plan, dedicated branch and
worktree, persistent goal, implementation continuation, the preceding
fast-forward of `main`, and local validated checkpoint commits after coherent
bounded tranches are green and their plan ledger is synchronized. This does
not authorize push, publication, release, PR creation, merge beyond the
already completed fast-forward, rebase, amend, reset, history rewriting,
branch deletion, or worktree removal.

## Reviewed Current Gaps

### The generic formal weak-kernel input is ready

`emdash3_2_weak_kernels.lp` already owns:

```text
WeakKernelAnnihilator(α,T)
WeakKernelFactorOperation(α,K)
WeakKernelFactorLaw(α,K,κ,factor)
ComputationalWeakKernel(α)
HasComputationalWeakKernels(C,S).
```

Annihilated test arrows are the internal fibre of ordinary postcomposition at
the selected zero arrow. Reindexing retains a whole Path functor, and selected
factors are explicitly not required to be unique. This is exactly the
algorithmic input required by the Freyd kernel construction.

### Generic kernels and cokernels are not formal owners yet

The active Lambdapi development has no generic `ComputationalKernel`,
`ComputationalCokernel`, `HasComputationalKernels`,
`HasComputationalCokernels`, `PreAbelianCategory`, monic, or epic structure.
The TypeScript doctrine registry contains `preabelian-category` and
`abelian-category` descriptors, but these are only role requirements. They do
not supply universal constructions or laws.

### The Freyd constructor's cokernel role is metadata ahead of execution

The generic TypeScript `freydConstructor()` descriptor records an introduced
`cokernel` role, while the operational polynomial Freyd model presently
registers only category and additive operations. The historical field-module
reference model computes kernels, cokernels, lifts, and colifts directly over
a field, but its category-operation registry exposes only whole kernel,
kernel-object, whole cokernel, and cokernel-object. It is useful differential
evidence, not yet the desired complete provider.

### The concrete formal base category lacks a packaged additive structure

The TypeScript finite-free polynomial category is operationally additive, but
the Lambdapi `CommRingFiniteFree_cat(R)` currently has no selected
`PreadditiveCategory` or `AdditiveCategory` package. Matrix addition,
subtraction, block sums, identities, composition, and their laws already
exist, so this is a structural packaging prerequisite rather than a missing
matrix algorithm.

An arbitrary abstract `CommRing` also cannot be assigned weak kernels
unconditionally. The formal Freyd construction must therefore accept:

```text
W : HasComputationalWeakKernels(CommRingFiniteFree_cat(R), S)
```

as a capability input. A CAS-backed selected ring may provide that capability
through the explicit trust/delegation boundary; no theorem in this plan turns
all abstract commutative rings into coherent rings.

### The concrete polynomial Freyd (co)kernel algorithms are missing

For a Freyd morphism represented by a relation-preserving matrix and witness,
there is currently no operational:

```text
kernel
kernel-object
kernel-embedding
kernel-lift
cokernel
cokernel-object
cokernel-projection
cokernel-colift.
```

The `preabelian-category` doctrine currently asks only for whole `kernel` and
`cokernel` roles. This goal must review and strengthen that surface so the
universal operations are real derived roles rather than inaccessible fields
inside an opaque result.

## Internal Computational Formulation

### Annihilators and coannihilators

For `alpha : A -> B` in a preadditive category, retain the existing
annihilator:

```text
Ann_alpha(T)
  := HFiber(
       Hom(T,A) --(alpha o -)--> Hom(T,B),
       0_(T,B)).
```

Introduce only its genuine dual:

```text
Coann_alpha(T)
  := HFiber(
       Hom(B,T) --(- o alpha)--> Hom(A,T),
       0_(A,T)).
```

Both are internal fibres of the existing Hom actions. No hand-written
commuting triangle, square, Boolean equation, or parallel cone grammar is
allowed. Their test-object actions should be retained through whole Path
functors whenever the existing Hom owner provides them.

### Kernel factor spaces and uniqueness

For a candidate `kappa : K -> A` and an annihilated cone
`cone : Ann_alpha(T)`, define the space of factors:

```text
KernelFactorSpace(kappa,cone)
  := HFiber(
       Hom(T,K) --(kappa o -)--> Hom(T,A),
       arrow(cone)).
```

A computational kernel requires this space to be contractible for every
`T` and `cone`. Its center is the selected kernel lift and its contraction is
the uniqueness law. Thus the structure contains computational data without
duplicating a separate existential proof:

```text
ComputationalKernel(alpha)
  := (K, kappa, alpha o kappa = 0,
      forall T cone, IsContr(KernelFactorSpace(kappa,cone))).
```

Readable object, embedding, lift, reconstruction, and uniqueness projections
must be exposed. The ordinary proposition-valued existence view is a
truncation of the selected computational structure.

### Cokernel factor spaces

Dually, for `q : B -> Q` and `cone : Coann_alpha(T)`:

```text
CokernelFactorSpace(q,cone)
  := HFiber(
       Hom(Q,T) --(- o q)--> Hom(B,T),
       arrow(cone)).
```

`ComputationalCokernel(alpha)` requires every such factor space to be
contractible. Its center gives the selected colift. The implementation should
reuse `Op_cat` for theorem-level duality where that retains the required
owners, but may expose a narrow mirrored stable projection surface when
opposite normalization would erase the discriminator needed by runtime
consumers. No propositional equality bridge between allegedly identical
primitive theories is permitted.

### Whole category capabilities

Package:

```text
HasComputationalKernels(C,S)
HasComputationalCokernels(C,S)
PreAbelianCategory(C)
  := AdditiveCategory(C)
     + HasComputationalKernels(C,...)
     + HasComputationalCokernels(C,...).
```

The exact record layout must reuse the active `PreadditiveCategory` and
`AdditiveCategory` owners. It must not duplicate their operations or hide
incompatible preadditive structures in separate fields.

## Computational Weak Pullbacks

For a cospan:

```text
A --alpha--> B <--gamma-- C
```

form the additive difference map:

```text
[alpha,-gamma] : A + C -> B.
```

Given a computational weak kernel `(K,kappa)` of this map, define:

```text
p := pi_1 o kappa : K -> A
q := pi_2 o kappa : K -> C.
```

The weak-kernel annihilation equation and preadditive cancellation derive:

```text
alpha o p = gamma o q.
```

For every equalizing pair `a : T -> A`, `c : T -> C`, the pairing
`<a,c> : T -> A + C` is annihilated by `[alpha,-gamma]`; the selected weak-
kernel factor supplies the induced weak-pullback map. Its two projection laws
are derived. No uniqueness is claimed.

Expose one whole `ComputationalWeakPullback` result plus derived object,
projections, and selected lift operations. On the TypeScript side, register a
derived operation whose prerequisites are additive biproducts and the whole
weak-kernel operation; do not introduce a second matrix algorithm.

## Constructive Freyd Cokernels

For a raw Freyd morphism represented as:

```text
{alpha,rho_alpha} : (R_A --rho_A--> A) -> (R_B --rho_B--> B),
```

Construction 3.6 forms the cokernel presentation by adjoining the morphism
datum to the target relations:

```text
[rho_B, alpha] : R_B + A -> B.
```

The projection is represented by `id_B`; its relation witness is a canonical
injection. A zero-composite witness for a test morphism supplies the relation
witness of the induced colift. Correctness must include:

- well-formedness of the constructed presentation and raw morphisms;
- the selected quotient class of the projection;
- annihilation in the Freyd quotient;
- selected colift reconstruction;
- uniqueness in the quotient; and
- the local fact that the selected projection is epic.

This construction is unconditional for every additive base category. It must
not call the weak-kernel provider.

## Constructive Freyd Kernels

Construction 3.10 uses two weak pullbacks in the base additive category. The
first combines the target relation arrow `rho_B` with the morphism datum
`alpha`; the second combines its induced projection with `rho_A`. The exact
matrix orientation and block convention must be recovered from the current
row/column representation and checked in owner-position probes before code is
promoted; remembered diagram orientation is not authority.

The construction must produce:

- a selected kernel presentation;
- a relation-preserving raw kernel embedding and witness;
- its quotient class;
- annihilation in the Freyd quotient;
- a selected lift for every annihilated Freyd test morphism, using the supplied
  zero-composite witness in the weak-pullback factorization;
- reconstruction in the quotient;
- uniqueness in the quotient; and
- the local fact that the selected embedding is monic.

The zero-composite witness is genuine input to the induced morphism datum. It
must remain a typed internal agreement/path object, not be erased into a
Boolean zero test.

## TypeScript Category/CAS Architecture

### Generic provider interface

Define a backend-neutral Freyd construction provider parameterized by:

- an additive computable category;
- its zero, addition, negation, biproduct, pairing, and projection roles;
- a whole computational weak-kernel provider with selected factors; and
- the Freyd raw-morphism/agreement representation and quotient equality
  operations.

The generic interface should describe the algorithms and dependencies even
when a particular runtime cannot decide all quotient equalities. The
finite-free polynomial provider is the first authoritative implementation.

Do not force an entirely new parallel Freyd object/morphism grammar merely to
obtain genericity. Reuse the current presentation representation and extract
the smallest capability interface that its algorithms actually consume. A
fully generic formal `Freyd_cat(P)` may be added only if owner audit shows it
can reuse the current groupoidification/quotient owners without duplicating
the specialized formal category.

### Complete operation families

Register whole operations and derived observations:

```text
weak-pullback
weak-pullback-object
weak-pullback-projection-1
weak-pullback-projection-2
weak-pullback-lift

kernel
kernel-object
kernel-embedding
kernel-lift

cokernel
cokernel-object
cokernel-projection
cokernel-colift.
```

Strengthen `PREABELIAN_DOCTRINE` so qualification requires the usable
object/structural-arrow/factor operations, not only inaccessible whole result
boxes. Preserve one whole owner for each universal construction and derive
projections through category methods.

### Compiler and reference execution

Every public categorical operation must have:

- a runtime schema;
- category-method registration with exact prerequisites;
- a backend-neutral algebra-operation lowering;
- TypeScript reference implementation;
- computation-graph execution; and
- deterministic serialization or comparison appropriate to the result.

The field-module implementation may be expanded to expose its existing
kernel-lift and cokernel-colift functions through the same role family and
used as differential/conformance evidence. It must not substitute field
linear algebra for polynomial Freyd computation.

### Differential backends

Singular or another installed CAS may compare selected presented-module
kernels/cokernels when a stable adapter is useful. Such comparison is optional
and non-authoritative. The native TypeScript construction, its retained
witnesses, and checked quotient equations remain the ordinary execution path.

## Formal Capability And Proof-CAS Bridge

The generic formal construction should consume:

```text
S : AdditiveCategory(P)
W : HasComputationalWeakKernels(P, preadditive(S)).
```

For the current concrete presentation category, first package the existing
finite-free matrix operations as the required formal additive structure. Then
construct the Freyd kernel/cokernel terms parameterized by `W` and return a
`PreAbelianCategory` structure on the existing
`CommRingFreydPresentation_cat(R)`.

The TypeScript polynomial provider already supplies the runtime operation for
every supported matrix. Lambdapi must not infer a universal provider for an
arbitrary `CommRing`. A selected CAS-backed capability may be represented at
the explicit trust/delegation boundary. Concrete proof-CAS consumers should
reify the actual presentations, structural matrices, lifts/colifts, and exact
annihilation/reconstruction equations produced by the operations.

Named finite equations do not by themselves construct a closed dependent
function over every formal arrow. Conversely, the absence of a formal proof
of Gröbner correctness does not prevent the proof assistant from requesting,
naming, and using the CAS-provided data under the explicit capability
boundary.

## No Manual Diagram Fields

Every apparent commuting square or triangle in the Freyd formulas must arise
from existing internal structure:

- a relation-preserving raw morphism;
- a morphism-agreement witness;
- an `HFiber` point/path;
- ordinary composition/addition/zero paths; or
- a whole Hom action.

Do not introduce a semantic record containing an independently written square
equation. Do not replace a typed witness with a Boolean. Keep quotient
equalities at the existing groupoidification and set-truncation owners.

## Computation And Rewrite Policy

- Generic category identity, composition, addition, negation, biproduct, and
  Hom action remain their current runtime owners.
- New runtime rewrites are limited to constructor-visible beta projections of
  new stable whole construction heads.
- Transparent semantic definitions are preferred for factor spaces,
  annihilators, duality adapters, and theorem-level packages.
- Proof-time unifiers may connect a rigid usability head to an already
  normalized semantic body when neither orientation should become a runtime
  normal form.
- Every proposed rewrite or unifier follows owner-position probes, inferred-
  slot hygiene, warning comparison, typed `eq_refl` validation for unifiers,
  and positive/noncollapse reviewers.
- Warnings are diagnostic evidence, not an automatic veto; timeouts,
  subject-reduction failures, retained-action loss, or unjoinable computation
  are rejection signals.
- Whole operations must not be capped at object-level observations when a
  derived structural morphism or factor operation remains a consumer.

## Completion Boundary

This goal is complete only when:

- generic internal computational kernel and cokernel structures, readable
  projections, proposition views, and whole capability packages check;
- the finite-free formal base has the required additive package or an exact
  documented replacement prerequisite;
- computational weak pullbacks derive from weak kernels and additive
  biproducts, with projection/reconstruction consumers;
- polynomial Freyd cokernel and kernel whole results compute for nontrivial
  presentations;
- annihilation, lift/colift reconstruction, and quotient uniqueness are
  checked rather than described;
- complete category operation families, compiler lowerings, reference
  implementations, and graph execution are active;
- the polynomial Freyd model genuinely qualifies as `preabelian-category`;
- the generic formal construction consumes an explicit weak-kernel capability
  and selected concrete proof-CAS consumers check;
- zero, identity, degenerate, nontrivial, foreign-ring, unsupported-provider,
  cancellation, limits, and deterministic replay boundaries are covered;
- every new Lambdapi rule has classified warning and strict-LHS evidence;
- affected examples, catalogs, health, standing authorities, focused tests,
  typecheck/lint, and the proportional shared integration gate are current;
  and
- every ledger row is implemented, rejected with durable evidence, or
  explicitly deferred behind a concrete prerequisite.

The goal does **not** complete merely because `PREABELIAN_DOCTRINE` is selected
or a kernel/cokernel result type exists.

## Deliberate Non-Goals

This goal does not include:

- the claim that every arbitrary `CommRing` has weak kernels;
- a proof of Hilbert's basis theorem or Gröbner correctness;
- general decidable lifts or colifts in the base category;
- Posur Construction 3.13 lifts along arbitrary monomorphisms;
- Posur Construction 3.14 colifts along arbitrary epimorphisms;
- image, coimage, or coimage-image isomorphism roles;
- `AbelianCategory` qualification;
- exact sequences, homology, resolutions, derived categories, or spectral
  sequences;
- an unrelated generic arrow/lax-square grammar;
- path-cubical/global-strictness integration;
- print/book/release work; or
- push, publication, PR, history rewriting, branch cleanup, or worktree
  removal.

The immediate successor goal should implement the normal-mono/normal-epi
operations of Constructions 3.13 and 3.14, derive images/coimages and their
comparison isomorphism, and finish the constructive Freyd-to-Abelian theorem.

## Feasibility And Rejection Signals

The goal is strongly feasible because:

- original-column syzygies and arbitrary selected weak-kernel factors are
  already operational;
- finite-free zero/add/negate/biproduct and block-matrix operations are active;
- raw Freyd presentations, relation-preserving morphisms, agreement witnesses,
  quotient paths, and additive operations are active;
- the constructive formulas require only weak pullbacks and existing Freyd
  witnesses;
- the field-module reference implementation already exercises kernel,
  cokernel, lift, and colift shapes; and
- the category-operation planner, compiler, graph, proof-CAS, and live
  Lambdapi bridges are active.

Refine or reject a candidate when it:

- treats a weak-kernel lift as unique;
- creates a Freyd kernel without consuming the zero-composite witness needed
  for its induced morphism datum;
- tests commutativity only by Boolean equality;
- constructs only kernel/cokernel objects without structural arrows and
  factors;
- declares pre-Abelian structure from metadata rather than qualified roles;
- computes polynomial Freyd kernels by field-only inverses;
- claims a universal formal polynomial provider from finitely many named
  equations;
- duplicates the existing Freyd quotient or category operation grammars;
- caps whole Hom/equality action required by a real consumer;
- relies on broad hot-head runtime rewrites for `id` or `comp_fapp0`;
- violates owner-position inferred-slot SOP; or
- makes progress depend on an unrelated aggregate or orthogonal branch.

## Implementation Ledger

| ID | State | Dependencies | Required result |
|---|---|---|---|
| `FPA-PLAN-0` | complete; checkpoint `4059161` | baseline `c781a42` | living plan, isolated branch/worktree, fast-forward evidence, explicit Git/scope boundary, persistent goal |
| `FPA-AUDIT-1` | complete; checkpoint pending | plan | exact formal/TypeScript owners, Posur/CAP formula orientation, current role/provider gaps, rejection signals, bounded baseline |
| `FPA-BASE-ADD-2` | ready | finite-free matrix laws | formal `PreadditiveCategory`/`AdditiveCategory` package for `CommRingFiniteFree_cat(R)` without duplicate operations |
| `FPA-UNIVERSAL-3` | active | preadditive owners | generic internal computational kernel/cokernel factor spaces, contractibility, projections, proposition and whole capability views |
| `FPA-WEAK-PB-4` | blocked on base + weak kernels | additive biproduct + weak kernels | derived whole computational weak pullback with projections and selected factor |
| `FPA-COKERNEL-5` | blocked on audit | Freyd presentation/additive owners | unconditional Freyd whole cokernel, object, projection, colift, annihilation, reconstruction, uniqueness/epic evidence |
| `FPA-KERNEL-6` | blocked on weak pullbacks | Freyd presentation + base capability | Freyd whole kernel, object, embedding, lift, annihilation, reconstruction, uniqueness/monic evidence |
| `FPA-CATEGORY-7` | blocked on kernel/cokernel | operation/doctrine engine | complete operation families, strengthened pre-Abelian doctrine, provider qualification, compiler lowering, reference/graph execution |
| `FPA-FORMAL-8` | blocked on universal + concrete constructions | explicit weak-kernel capability | capability-parameterized formal Freyd pre-Abelian package and selected proof-CAS consumers |
| `FPA-DIFFERENTIAL-9` | optional after native construction | stable external adapter | non-authoritative field-module and/or Singular comparison without replacing native data |
| `FPA-CLOSE-10` | blocked on all required rows | all required rows | standing docs, warning/LHS/catalog/health evidence, focused/static/integration gates, exact checkpoints and successor boundary |

Rows may be split or reordered when dependencies permit. A row may be rejected
or deferred only with durable evidence and a concrete replacement or
prerequisite; difficulty or warning count alone is insufficient.

## Decision Ledger

| ID | State | Decision |
|---|---|---|
| `D-FPA-001` | accepted | The immediate theorem boundary is computational pre-Abelian structure: genuine Freyd kernels and cokernels with universal operations, before normality and the full Abelian theorem. |
| `D-FPA-002` | accepted | Generic kernel/cokernel universality is formulated by contractibility of internal `HFiber` factor spaces, not manual cone diagrams. |
| `D-FPA-003` | accepted | Weak pullbacks are derived from weak kernels of `[alpha,-gamma]` and additive biproducts; they are not a second primitive matrix algorithm. |
| `D-FPA-004` | accepted | Freyd cokernels are unconditional; Freyd kernels consume the base weak-kernel capability through weak pullbacks. |
| `D-FPA-005` | accepted | The generic formal construction is capability-parameterized. No arbitrary abstract `CommRing` receives weak kernels by declaration. |
| `D-FPA-006` | accepted | The existing Freyd presentation/agreement/groupoidification quotient remains the formal and operational carrier; no parallel quotient grammar is introduced. |
| `D-FPA-007` | accepted | Whole universal-construction results own computation; object, structural arrow, and factor operations are derived and remain separately registerable for usability. |
| `D-FPA-008` | accepted | `PREABELIAN_DOCTRINE` must require the usable kernel/cokernel role families, not only whole boxes. |
| `D-FPA-009` | accepted | The field-module implementation is differential evidence only; polynomial Freyd computation must not use field-only splittings. |
| `D-FPA-010` | accepted | Lifts along arbitrary monomorphisms, colifts along arbitrary epimorphisms, image/coimage comparison, and `AbelianCategory` belong to the successor goal. |
| `D-FPA-011` | accepted after owner audit | The first formal theorem targets the existing `CommRingFreydPresentation_cat(R)` and takes an explicit finite-free weak-kernel capability. A second generic formal Freyd quotient is not introduced without a consumer that cannot reuse the active presentation/agreement/groupoidification carrier. |
| `D-FPA-012` | accepted after upstream audit | In the repository's column convention, the cokernel relation is `[rho_B,alpha]`; the kernel relation is the second biased weak-fibre-product projection and its embedding datum is the first projection. The zero-composite agreement remains typed input even when upstream CAP retrieves it indirectly. |
| `D-FPA-013` | accepted after formal audit | Genuine kernel/cokernel uniqueness is contractibility of direct Hom factor fibres. The selected centre, fibre path, and contraction path derive lift/colift, reconstruction, and uniqueness without a manual universal-square record. |

## Validation Matrix

Use proportional, bounded checks. Do not run print, book, release, or unrelated
repository aggregates.

### Plan and audit

- exact staged/unstaged diff review;
- `git diff --check`;
- Markdown/link/header/reference hygiene;
- workspace contract;
- root TypeScript typecheck and nearest focused Freyd/weak-kernel suites;
- bounded checks of the current formal finite-free, Freyd additive, and weak-
  kernel owners.

### TypeScript implementation rows

- affected focused tests after every coherent slice;
- root typecheck and affected lint;
- explicit tests of whole and derived category methods;
- compiler-plan and reference-engine execution;
- computation-graph execution and deterministic replay;
- one complete `check:ts` only when the shared doctrine/public/compiler
  boundary is otherwise green and ready for checkpoint/integration.

### Lambdapi implementation rows

- smallest owner-position probe with positive and noncollapse consumers;
- every invocation bounded to at most 90 seconds;
- quiet and warning-enabled source checks;
- exact import-union versus candidate warning classification;
- strict inferred-slot/LHS audit;
- focused reviewer examples;
- registered checks/catalog refresh;
- health source snapshot refresh after meaningful architecture changes;
- bounded CI only at the coherent semantic integration boundary.

### External differential rows

- pure deterministic script/adapter tests are mandatory if an adapter is
  added;
- real external-process tests remain explicitly environment-gated;
- disagreement remains observable and non-authoritative;
- no external CAS is required for ordinary native execution.

## Sources And Design References

- Sebastian Posur, *A constructive approach to Freyd categories*, especially
  Definition 3.4 and Constructions 3.6, 3.10, 3.13, and 3.14:
  <https://arxiv.org/html/1712.03492v1>.
- CAP project overview and doctrine/operation decomposition:
  <https://homalg-project.github.io/docs/CAP_project-based/>.
- FreydCategoriesForCAP documentation:
  <https://homalg-project.github.io/CAP_project/FreydCategoriesForCAP/>.
- Completed computational weak-kernel plan:
  `docs/TYPESCRIPT_EMDASH_FREYD_COMPUTATIONAL_WEAK_KERNELS_PLAN.md`.
- Completed additive Freyd plan:
  `docs/TYPESCRIPT_EMDASH_FREYD_ADDITIVE_BIPRODUCTS_PLAN.md`.
- Completed prerequisite owner audit:
  `docs/TYPESCRIPT_EMDASH_FREYD_PREABELIAN_OWNER_AUDIT.md`.

These references guide formulas and operation decomposition. Active source,
focused diagnostics, and repository SOP remain implementation authority.

## Persistent Goal Launch Prompt

Continue `TS-EMDASH-FREYD-PREABELIAN-COMPUTATION` from the living plan in
`docs/TYPESCRIPT_EMDASH_FREYD_PREABELIAN_COMPUTATION_PLAN.md`. Treat active
source and the root/nested SOP as authority. Work only in
`/home/user1/emdash1-freyd-preabelian-v1` on branch
`goal/freyd-preabelian-computation-v3.2`, preserving baseline
`c781a42972a3e91f60a79bfd95989ca4dca4aaac` as comparison evidence. Resume
the first dependency-ready ledger row and revise the plan whenever probes
refine the architecture. Preserve internal `HFiber` universal properties,
contractible factor spaces, selected weak-kernel nonuniqueness, derived weak
pullbacks, typed Freyd witnesses, quotient equality, whole universal-
construction owners, separate derived usability roles, backend-neutral
category/CAS operations, explicit weak-kernel capability inputs, generic
identity/composition ownership, owner-position probing, warning
classification, strict LHS audits, retained higher action, and proportional
validation. Local validated checkpoint commits are authorized after coherent
bounded tranches are green and the exact staged diff plus ledger are
synchronized. Do not push, merge, publish, release, create a PR, amend,
rebase, reset, rewrite history, delete a branch, or remove a worktree. Do not
integrate orthogonal path-cubical/global-strictness work. Do not claim
arbitrary-`CommRing` weak kernels, `AbelianCategory`, image/coimage comparison,
exactness, or homology. The goal is complete only when every scoped row is
implemented, rejected with durable evidence, or explicitly deferred behind a
concrete prerequisite, and all affected authorities are synchronized.
