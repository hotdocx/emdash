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
| `FPA-AUDIT-1` | complete; checkpoint `0bdd3b5` | plan | exact formal/TypeScript owners, Posur/CAP formula orientation, current role/provider gaps, rejection signals, bounded baseline |
| `FPA-BASE-PREADD-2A` | complete; checkpoint `c0ce415` | finite-free matrix laws | formal `PreadditiveCategory` package for `CommRingFiniteFree_cat(R)` without duplicate operations |
| `FPA-BASE-ADD-2B` | complete; checkpoint `6839fe9a` | finite-free preadditivity + direct sums | selected binary products, terminal zero, Cartesian and `AdditiveCategory` packages for `CommRingFiniteFree_cat(R)` |
| `FPA-UNIVERSAL-3` | complete; checkpoint `66d2687` | preadditive owners | generic internal computational kernel/cokernel factor spaces, contractibility, projections, proposition and whole capability views |
| `FPA-WEAK-PB-4` | complete; checkpoint `ba573800` | additive biproduct + weak kernels | derived whole computational weak pullback with projections and selected factor |
| `FPA-COKERNEL-NATIVE-5A` | complete; checkpoint `3625a254` | Freyd presentation/additive owners | native unconditional Freyd whole cokernel, object, projection, witness-retaining colift, annihilation, reconstruction, quotient uniqueness |
| `FPA-COKERNEL-FORMAL-5B` | complete at witness-enriched boundary; checkpoint `4cd1348c`; closed quotient package deferred behind effective path/witness decoding | raw formal presentation/agreement owners | formal cokernel presentation/projection, witnessed colift, annihilation, reconstruction and uniqueness; no fabricated decoder |
| `FPA-KERNEL-NATIVE-6A` | complete; checkpoint `6d0ef4c0` | polynomial Freyd presentation + weak pullbacks | native Freyd whole kernel, object, embedding, two-stage lift, annihilation, reconstruction, quotient uniqueness |
| `FPA-KERNEL-FORMAL-6B` | complete at witness-enriched boundary; checkpoint `18d96719`; closed quotient package subject to effective path/witness decoding | formal witnessed weak pullbacks + explicit zero agreement | formal kernel presentation/embedding/two-stage lift, annihilation, reconstruction and monic uniqueness |
| `FPA-CATEGORY-7` | complete; checkpoint `e9bc341a` | operation/doctrine engine | complete operation families, strengthened pre-Abelian doctrine, provider qualification, compiler lowering, reference/graph execution |
| `FPA-FORMAL-8` | complete at witnessed boundary; checkpoint `ddbcf9e8`; closed quotient package gated by effectiveness | explicit weak-kernel capability + witnessed constructions | capability-parameterized witnessed formal Freyd pre-Abelian surface and selected proof-CAS consumers without fabricated quotient decoder |
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
| `D-FPA-014` | accepted after universal probe | Cokernel coannihilators and factor spaces are transparent direct dual definitions over precomposition. This is a rule-free mirrored semantic surface, not a duplicated runtime theory or propositional equality bridge; it retains covariant test-object Path action. |
| `D-FPA-015` | accepted after finite-free preadditive probe | Matrix zero/add/negate and abelian-group laws are reused definitionally. Generic `comp_fapp0` remains the runtime owner; both bilinearity paths pass through the existing generic-to-transparent matrix-composition comparison. No rewrite/unifier or parallel matrix operation is added. |
| `D-FPA-016` | accepted after finite-free product probes | The whole direct-sum functor owns the product object/action. Narrow stable heads expose matrix projections, vertical pairing, and the terminal zero arrow; generic triangular/terminal theories retain whole transfors and runtime beta/eta. All new warning inventories equal their import unions. |
| `D-FPA-017` | accepted during terminal audit | Zero-row matrix uniqueness is shared base algebra, so its unchanged proof moves from the Freyd terminal module to `emdash3_2_commutative_algebra_matrix_zero_rows.lp`; both finite-free and Freyd terminal constructions reuse that one owner. |
| `D-FPA-018` | accepted after weak-pullback probes | `WeakPullbackCone(alpha,gamma,T)` is the existing annihilator fibre of `[alpha,-gamma]` on one arrow `T -> X+Z`. The usual two legs are projections, and their reconstruction laws derive from one combined weak-kernel factor path. This is more internal than a record containing a separately written square. |
| `D-FPA-019` | accepted after native weak-pullback tests | The polynomial implementation concatenates the columns of `alpha` and `-gamma`, invokes the existing whole weak-kernel solver once, and projects its result. Compatible test pairs are vertically paired and sent to the existing factor operation. No second syzygy algorithm is registered. |
| `D-FPA-020` | accepted after native cokernel tests | Polynomial Freyd cokernels adjoin the morphism columns to the target relation module. Projection datum is ambient identity; a retained zero-composite agreement makes the colift well-defined, and quotient congruence verifies reconstruction and uniqueness. No weak-kernel call occurs. |
| `D-FPA-021` | accepted after formal cokernel audit | The current set-truncated Freyd Hom exposes agreement witnesses only in the forward direction. A quotient equality does not yet decode constructively to the raw target-factorization witness needed to build a colift. Do not fabricate that decoder, use choice, or postulate a closed `ComputationalCokernel`; first implement witness-enriched formal operations and gate quotient packaging on an effective-quotient theorem. |
| `D-FPA-022` | accepted after formal witnessed-cokernel probe | The witness-enriched construction is fully internal: relation matrix `[R_Q,F]`, projection witnesses `inl`, annihilation witness `inr`, and colift witness `[W_h,H_0]`. Existing agreement-to-path machinery proves quotient annihilation, reconstruction, and uniqueness without any runtime rule. |
| `D-FPA-023` | accepted after compatibility/cone probes | Difference-zero and conventional equalizing equations are two theorem-level views of one weak-pullback carrier. Generic abelian cancellation derives `alpha o p = gamma o q`; pairing plus bilinearity turns an explicit equality back into the annihilator cone. |
| `D-FPA-024` | accepted after native kernel tests | Polynomial Freyd kernels use exactly two existing weak-pullback solves. The zero-composite agreement witness feeds the first induced map; the test morphism's retained relation witness feeds the second. The second first projection is the kernel relation map and the first first projection is the embedding datum. |
| `D-FPA-025` | accepted after formal witnessed-kernel probes | Formal Construction 3.10 is parameterized by the finite-free weak-kernel capability. The zero agreement and source relation square construct the two lift cones. For uniqueness, the difference between a competing and selected lift plus the competing reconstruction witness forms a second-stage cone whose factor is exactly the Freyd agreement witness. |
| `D-FPA-026` | accepted after category-provider tests | `PREABELIAN_DOCTRINE` requires whole kernel/cokernel plus object, embedding/projection, and lift/colift roles. The field-polynomial Freyd provider qualifies only after every role has a plannable method; uniqueness remains checked inside the whole results and explicit native functions. |
| `D-FPA-027` | accepted after provider boundary tests | Operational pre-Abelian qualification is available only for polynomial rings with a field coefficient provider. The ordinary additive Freyd model remains valid over its broader ring boundary and is not silently promoted. |
| `D-FPA-028` | accepted after formal capability probe | `CommRingFreydWitnessedPreAbelian(R,W)` packages the exact existing Freyd additive structure and canonical kernel/cokernel law families for all raw presentation morphisms. Tests retain explicit zero/reconstruction agreements, so the package is constructive but intentionally distinct from closed quotient-level `PreAbelianCategory`. |
| `D-FPA-029` | accepted after selected-equation consumer | The proof-CAS bridge reuses the existing formal presentation-morphism and presentation-agreement realizations. It replays the actual kernel, kernel-lift, cokernel, and cokernel-colift operations and adopts eight exact structural, annihilation, and reconstruction equations; no parallel matrix-claim grammar or finite-observation-to-ring-capability promotion is added. |
| `D-FPA-030` | accepted after zero-relation regression | The finite-module Core signature for matrix composition previously returned a `rows x middle` classifier instead of `rows x columns`. Selected Freyd agreements with zero relation rank exposed the latent de Bruijn-index error. The shared signature owner now uses the actual columns binder and carries revision `v2`; the focused lower bridge matrix and emitted Lambdapi consumer pass. |

## Implemented Generic Universal Layer

`emdash3_2_kernels_cokernels.lp` now implements the generic internal layer
selected by the audit. It adds the coannihilator `HFiber` and its covariant
whole Path reindexing, direct kernel/cokernel factor spaces, selected
computational structures whose every factor space is contractible, and
readable projections for object, structural arrow, annihilation,
lift/colift, reconstruction, and uniqueness.

Ordinary `Kernel` and `Cokernel` existence are propositionally truncated from
the selected structures. Whole `HasComputationalKernels`,
`HasComputationalCokernels`, `HasKernels`, and `HasCokernels` packages are
active, as is the thin selected `PreAbelianCategory` package over one existing
`AdditiveCategory`. The module adds no rewrite or unification rule.

`examples/kernels_cokernels.lp` checks retained coannihilator Path action,
selected lifts/colifts, both reconstruction paths, both uniqueness paths, and
the additive projection of pre-Abelian data. Source and reviewer checks pass
within the bounded gate. The strict LHS audit reports zero clauses. Warning-
enabled comparison is exactly neutral at `1,386 = 1,217 + 169` against the
sole import owner `emdash3_2_weak_kernels.lp`. The module and reviewer are
registered; at that checkpoint the catalog and 393-file source-metrics health
snapshot were refreshed.

## Implemented Finite-Free Preadditive Base

`emdash3_2_commutative_algebra_finite_free_preadditive.lp` now constructs the
first selected `PreadditiveCategory` on `CommRingFiniteFree_cat(R)`. Nested
`finite_family_is_set` witnesses establish matrix-Hom setness. The Hom
abelian-group structure reuses `comm_ring_matrix_zero`,
`comm_ring_matrix_add`, `comm_ring_matrix_neg`, and their checked laws.

Right and left bilinearity start from generic category composition, pass
through `comm_ring_finite_free_comp_fapp0_transparent_path`, apply the existing
transparent matrix distributivity path, and reframe both summands back to
generic composition. The module is rule-free, strict-LHS clean, and exactly
warning-neutral at `1,274 = 1,117 + 157` against its import union.
`examples/commutative_ring_finite_free_preadditive.lp` checks definitional
zero/add/negate observations and both generic distributivity paths. The module
and reviewer are registered, and the current health snapshot covers 395
files.

## Implemented Finite-Free Additive Base

The finite-free direct-sum functor is now selected as a genuine whole binary
product. Stable point observations reduce to `comm_ring_matrix_proj1`,
`comm_ring_matrix_proj2`, and `comm_ring_matrix_vertical`; the generic
triangular theory retains whole projection transfors, whole pairing, higher
action, and Došen beta/eta computation.

Rank zero is selected as terminal. Its Hom contractibility is centred at the
existing zero matrix and follows from the shared zero-row uniqueness lemma;
the terminal-arrow observation reduces to that zero matrix. The Cartesian
package transparently pairs these witnesses, and
`comm_ring_finite_free_additive` pairs the result with the exact finite-free
preadditive structure.

The binary-product warning inventory is exactly its import union at
`1,347 = 1,180 + 167`; terminal and final additive inventories are exactly
their import unions at `1,358 = 1,189 + 169`. Strict LHS audits are clean, and
the existing Freyd terminal source/reviewer remain green after moving the
zero-row lemma to its lower owner. All five new owners and the focused reviewer
are registered; the refreshed health snapshot covers 401 files.

## Implemented Computational Weak Pullbacks

`emdash3_2_computational_weak_pullbacks.lp` transparently defines the product
object, difference arrow, weak-pullback structure, projected legs, encoded
cone, selected lift, combined reconstruction, both projected reconstruction
paths, and whole `HasComputationalWeakPullbacks` capability. A whole
`HasComputationalWeakKernels` value constructs the latter pointwise. The
module adds no rule or unifier and inherits the nonuniqueness of weak-kernel
factors.

`algebra_polynomial_weak_pullback.ts` implements the same derivation for
finite-free polynomial maps. It verifies the selected projections equalize
the cospan, rejects malformed or incompatible tests, pairs compatible test
maps, delegates the sole solve to `algebraPolynomialWeakKernelFactor`, and
checks combined plus both projected reconstructions. Four focused tests cover
a nontrivial polynomial cospan, identity/zero boundaries, rejection paths,
progress, deterministic replay, and retained nonuniqueness. Category-operation
registration remains intentionally grouped with `FPA-CATEGORY-7`.

The formal module is rule-free, strict-LHS clean, and exactly warning-neutral
at `1,386 = 1,217 + 169` against its weak-kernel import owner. Source and
reviewer checks pass. The public TypeScript export, focused registration,
affected lint, typecheck, and `14/14` weak-kernel/weak-pullback matrix pass.
The refreshed health snapshot covers 403 files.

## Implemented Native Freyd Cokernels

`algebra_polynomial_freyd_cokernel.ts` implements Posur Construction 3.6 on
the active presentation carrier. Given a relation-preserving `f : P -> Q`, it
forms the presentation whose relation generators are `Q`'s existing relations
followed by the columns of `f`. The projection has the ambient identity datum.
Its composite with `f` is compared to zero by an explicit retained
presentation agreement.

A colift accepts a test starting at `Q`, computes and retains the agreement
that its composite with `f` is zero, reuses the test's ambient map on the new
presentation, and checks quotient reconstruction. A separate operation checks
any competing colift's reconstruction and then returns the quotient agreement
with the selected colift, giving computational uniqueness/epicity without
raw-matrix equality. Four focused tests cover a nontrivial `R/(x)` cokernel,
nonidentical but quotient-equal competing colifts, the zero boundary,
non-annihilated tests, invalid endpoints, frozen results, and rejection paths.

`emdash3_2_commutative_algebra_freyd_cokernels.lp` implements the formal
witness-enriched counterpart. Matrix horizontal/vertical block laws construct
the enlarged presentation, projection relation square, and the two canonical
relation injections. An explicit agreement for `h o f = 0` becomes the second
block of `[W_h,H_0]`, yielding a raw colift. Existing groupoidification and
truncation paths prove annihilation, reconstruction, and quotient uniqueness
of every explicitly reconstructing competing raw colift.

The module is rule-free, strict-LHS clean, and exactly warning-neutral at
`1,392 = 1,223 + 169` against `comm_ring_freyd_additive`. Source and focused
reviewer checks pass. This closes the useful witnessed computation while the
stronger closed quotient-level `ComputationalCokernel` package remains
explicitly deferred behind effective quotient-path decoding. The owner and
reviewer are registered, and the refreshed health snapshot covers 405 files.

## Implemented Native Freyd Kernels

The weak-pullback theorem layer now derives ordinary compatibility by generic
abelian cancellation and supplies `weak_pullback_cone_intro`, which maps an
explicit equalizing pair back into the existing difference-annihilator fibre.
These rule-free modules preserve one cone carrier and make formal Freyd kernel
inputs available without a manual square record.

`algebra_polynomial_freyd_kernel.ts` implements Posur Construction 3.10 with
two calls to the existing polynomial weak-pullback algorithm. The first
combines the morphism datum with target relations. The second combines its
first projection with source relations. Its first projection becomes the
kernel presentation relation map; the first construction's first projection
becomes the embedding datum, and the second projection is checked as the
embedding relation witness.

For a test morphism, the retained zero-composite agreement supplies the first
weak-pullback leg. The first selected lift composed with source relations and
the test's relation witness supply the second pair. The resulting presentation
morphism is checked for relation preservation, Freyd reconstruction, and
quotient uniqueness of competing lifts. Four focused tests cover a nontrivial
`(-y,x)` syzygy, both weak-pullback stages, progress, identity/zero boundaries,
non-annihilated and endpoint rejection, uniqueness, frozen data, and
deterministic replay. The two formal weak-pullback theorem modules are
rule-free, strict-LHS clean, and warning-neutral at
`1,386 = 1,217 + 169`; source/reviewer checks pass. The native kernel,
cokernel, and weak-pullback matrix passes `12/12`, along with typecheck and
affected lint. The refreshed health snapshot covers 407 files.

`emdash3_2_commutative_algebra_freyd_kernels.lp` now implements the
witness-enriched formal counterpart. It constructs both weak pullbacks from an
explicit `HasComputationalWeakKernels` value, exposes the kernel presentation
and embedding, proves annihilation from first-stage compatibility, and turns
an explicit zero-composite agreement plus the test relation witness into the
two lift cones. Existing agreement-to-path owners prove reconstruction.

Monic uniqueness is also computational: subtract the selected lift from a
competing lift, combine the competing reconstruction agreement with the
selected reconstruction path to obtain a second-stage equalizing pair, factor
it through the second weak pullback, and use that factor as the presentation
agreement witness. The rule-free source and focused reviewer pass; its warning
inventory is exactly its import union at `1,392 = 1,223 + 169`, and the strict
LHS audit is empty. The owner and reviewer are registered; the refreshed
health snapshot covers 409 files.

## Implemented Operational Pre-Abelian Category

`algebra_polynomial_freyd_preabelian_category.ts` extends the existing
additive polynomial Freyd model without changing its presentation or quotient
representation. It registers one whole kernel and one whole cokernel
primitive, then derives kernel object/embedding/lift and cokernel
object/projection/colift through the category-method planner. The model rejects
non-field coefficient providers before claiming the capability.

`PREABELIAN_DOCTRINE` now requires all eight usable roles rather than two
opaque whole boxes, and its dual map exchanges every kernel role with the
corresponding cokernel role. The new model qualifies that complete inherited
role set, appends one capability constructor to the categorical tower, lowers
all eight operations to backend-neutral algebra operations, and executes them
through the TypeScript reference engine. Focused tests cover qualification,
all derived plans, inherited additive operations, non-field rejection, whole
kernel/cokernel compilation, factor compilation, and graph execution.

The required shared `check:ts` gate reached completion on this fixed tree.
Workspace validation, root typecheck, and full lint pass. Every new doctrine,
weak-pullback, Freyd kernel/cokernel, pre-Abelian category, compiler, reference-
engine, and graph test passes in the consolidated corpus. Its failures are
exclusively inherited source-pin audits: the active-kernel digest split
between `e87ddf...` and `0a1177...`, displaced owner/rule positions in the
same historical transfer/pathout tests, and the existing overview-article
digest mismatch. No failure names a new operation, provider, model, or test;
the aggregate is not rerun.

## Implemented Witnessed Formal Capability And Proof–CAS Consumer

`emdash3_2_commutative_algebra_freyd_witnessed_preabelian.lp` now packages
the existing Freyd `AdditiveCategory`, all canonical witnessed kernels, and
all canonical witnessed cokernels. Its kernel family is parameterized by the
explicit finite-free weak-kernel capability `W`; the cokernel family remains
unconditional. For every raw presentation morphism, each family contains
quotient annihilation and, for every raw test with a zero-composite agreement,
selected reconstruction plus uniqueness against every raw competitor carrying
a reconstruction agreement. The whole package has readable additive,
kernel-family, and cokernel-family projections.

This closes the formal row at the honest constructive boundary. It does not
manufacture a function from arbitrary set-truncated paths to agreement
witnesses, so it is not silently coerced to the stronger generic
`PreAbelianCategory`. The source and reviewer are rule-free, pass bounded
checking, and have a strict-LHS count of zero. Their warning-enabled inventory
is identical to the current kernel import at
`1,392 = 1,223 critical pairs + 169 replaceable variables`.

`algebra_formal_freyd_preabelian.ts` supplies the concrete consumer. It
serializes the exact selected whole operation output and replays the native
pre-Abelian provider for kernel, kernel lift, cokernel, and cokernel colift.
For each result it reuses the established formal presentation-morphism law for
the structural arrow/factor and the established presentation-agreement law
for annihilation or reconstruction. All eight equations typecheck in the
TypeScript Core, all four actual operations replay and their eight claims are
explicitly adoptable, deterministic replay passes, and one focused emitted
Lambdapi probe checks all eight equations.

That consumer exposed and corrected one lower signature bug:
`bridge_comm_ring_matrix_comp` had used the bound `middle` dimension as the
result's column count. The v2 signature now returns `rows x columns`, as the
active Lambdapi operation does. The affected finite-module,
presentation-morphism, weak-kernel, and new Freyd bridge tests pass. This is a
shared signature correction, not a new runtime or Core owner.

The formal source and reviewer are registered. The generated catalog remains
strict and the source-metrics health snapshot is current for 411 files. A
resumable health invocation was stopped after process inspection showed it had
invalidated its predecessor identity and crossed into unrelated Gray-cube
checks; the report was refreshed in source-metrics-only mode instead. Fresh
bounded checks for the new owner, reviewer, warning inventory, emitted
consumer, and all affected lower TypeScript bridges provide the scoped
behavioral evidence.

The root workspace contract, TypeScript typecheck, and affected lint pass.
The focused finite-module, presentation-morphism, weak-kernel, Freyd bridge,
and pre-Abelian category matrix passes `15/15` ordinary tests with two
environment-gated live tests skipped; the separately enabled new live test
passes all `4/4` bridge tests and checks all eight equations in one bounded
Lambdapi process. The earlier completed `check:ts` result is carried forward
and is not rerun.

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
