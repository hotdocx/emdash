# TypeScript/emdash Computational Weak Kernels For Freyd Categories Plan

Date: 2026-09-01

Plan-ID: `TS-EMDASH-FREYD-COMPUTATIONAL-WEAK-KERNELS`

Status: active on a dedicated branch/worktree

Baseline: `c4baf61102d4dc27b68406fdc3536c82bf01896c`

Branch: `goal/freyd-computational-weak-kernels-v3.2`

Worktree: `/home/user1/emdash1-freyd-weak-kernels-v1`

Decision-Response-Evidence:

- `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a05dc9-1e06-7133-88dc-81e6f8496731`

## Purpose

This plan is the immediate capability-indexed successor to the completed
finite-direct-sum/additive-Freyd development. It implements computational weak
kernels in the finite-free polynomial matrix category underlying the Freyd
construction, exposes them through the TypeScript categorical/CAS engine, and
adds an internal Lambdapi weak-kernel formulation plus selected formal bridge
consumers.

For an arrow `alpha : A -> B` in an additive category, a computational weak
kernel consists of:

```text
K(alpha)                         : object
kappa_alpha : K(alpha) -> A      : weak-kernel arrow
alpha o kappa_alpha = 0          : annihilation

lift_alpha(tau,p) : T -> K(alpha)
kappa_alpha o lift_alpha(tau,p) = tau
```

for every `tau : T -> A` with `p : alpha o tau = 0`. The lift is selected but
need not be unique. This is the algorithmic notion required by the constructive
Freyd theorem: for an additive category `P`, its Freyd category `A(P)` is
Abelian exactly when `P` has weak kernels.

The intended vertical slice is:

```text
arbitrary original-column polynomial matrix F
  -> complete syzygy module of the original columns
  -> weak-kernel matrix K with F o K = 0
  -> reusable factorization H = K o U for every F o H = 0
  -> whole category operation and backend-neutral provider
  -> Singular differential oracle
  -> internal Hom-fibre weak-kernel interface
  -> selected computation-to-formal consumers
  -> later, separately gated Freyd weak-kernel-to-Abelian theorem.
```

This goal does **not** obtain an Abelian category by changing a doctrine label.
It supplies the concrete prerequisite which the later constructive theorem must
consume.

## Operational Baseline And Git Boundary

The branch starts from completed additive-Freyd checkpoint `c4baf61`. That
baseline already contains:

- full arbitrary-quotient Freyd preadditivity;
- flattened finite-family/vector/matrix direct sums;
- zero/direct-sum presentations and quotient descent;
- selected `BinaryProducts`, terminal zero, and Cartesian structure;
- generic `AdditiveCategory = PreadditiveCategory + CartesianCategory` with
  initiality, injections, copair beta/eta, and the biproduct identity; and
- an operationally qualified TypeScript polynomial Freyd additive category.

Historical `main` remains at its independent integration boundary. This goal
does not first fast-forward or mutate it. Orthogonal path-cubical and global-
strictness work remains excluded.

The user explicitly authorized this dedicated branch/worktree, living plan,
persistent goal, and continuation. Local validated checkpoint commits are
permitted after coherent bounded tranches are green and the exact staged diff
and ledger are synchronized. This authorization does not include push, merge,
publication, release, PR creation, amend, rebase, reset, history rewriting,
branch deletion, or worktree removal.

Fresh baseline evidence is green for:

- workspace setup and root TypeScript typechecking;
- the focused polynomial-module and direct polynomial-Freyd suites (`10/10`);
- `emdash3_2_additive_categories.lp`;
- `emdash3_2_commutative_algebra_finite_free_category.lp`;
- `emdash3_2_commutative_algebra_freyd_additive.lp`; and
- installed Singular `4.3.2`.

No repository-wide aggregate is part of the initial baseline.

## Reviewed Current Gap

### The existing capability is metadata only

`AlgebraPolynomialWeakKernelCapability` currently records:

```text
ring
basis = groebner-syzygy
operationalFieldCoefficients = true
claimsAbelianStructure = false.
```

It computes no weak-kernel object, arrow, annihilation equation, lift, category
method, compiler lowering, or formal artifact. It must be replaced or
subordinated to genuine executable capability evidence; retaining this record
as the primary result would not complete the goal.

### Existing Schreyer syzygies are necessary but insufficient

`algebraPolynomialModuleSchreyerSyzygies` computes verified relations among
the selected Gröbner-basis vectors in the induced Schreyer module. A weak
kernel of an arbitrary matrix requires the complete syzygy module of its
**original ordered columns** plus an algorithm that expresses every
annihilated test column in the selected syzygy generators.

The missing transformation layer must account for:

- Gröbner-basis transformation rows back to original columns;
- zero and redundant original columns omitted from the basis;
- pulled-back S-pair syzygies;
- relations expressing each original generator through the Gröbner basis;
- deterministic reduction of the resulting original-column syzygy module;
- membership coefficients used as weak-kernel lifts; and
- checked reconstruction equations.

Merely returning the current `syzygies.generators` would use the wrong source
free module and fail the universal factorization boundary.

### Implemented original-column syzygy result

`algebraPolynomialModuleOriginalSyzygies` now constructs the complete
original-column syzygy module without changing the existing Schreyer owner.
It computes the image Gröbner basis and its retained original-generator
transformation rows, pulls every Schreyer relation back through those rows,
and adds one `e_j`-minus-reconstruction relation for every original column.
The latter recovers literal zero columns, duplicate/redundant columns, and all
relations hidden when the original list is replaced by its basis.

All candidates live in one deterministic `term-over-position` free module
whose positions are exactly the original column indices. Each raw relation is
checked by recombination with the original columns. A final Gröbner basis of
that syzygy submodule is computed and checked again, while the result retains
the image basis, Schreyer data, pulled-back relations, original rewrites,
raw generators, final basis, operation counts, progress, and cancellation.

The focused suite now checks a three-column polynomial example with both a
Koszul and redundant-column relation, duplicate and zero columns, independent
identity columns, an empty source, reconstruction of every selected basis
element, immutable output, cancellation, and non-field rejection. Root
typechecking and the focused `8/8` module suite pass.

### No formal weak-kernel owner exists

The active Lambdapi library has `HFiber`, generic Hom pre/postcomposition,
preadditive zero arrows, and truncation, but no `WeakKernel` or
`ComputationalWeakKernel` classifier. The new interface must be internal and
must not introduce a hand-written commuting-triangle record.

## Internal Formal Architecture

### Annihilated maps are an internal Hom fibre

For `alpha : A -> B`, preadditive evidence `S`, and test object `T`, define:

```text
Ann_alpha(T)
  := HFiber(
       Hom(T,A) --(alpha o -)--> Hom(T,B),
       0_(T,B)).
```

An element is an arrow `tau : T -> A` together with its internal path
`alpha o tau = 0`. It is not a separately hand-written square or cone law.
The existing postcomposition functor remains the action owner.

The first formal audit must determine the smallest whole family assembly over
`Op(C)`. Preferred order:

1. derive the point classifier transparently from `HFiber`;
2. reuse `hom_con`/precomposition for test-object action;
3. retain a whole annihilator-family functor when existing varying-fibre
   infrastructure suffices; and
4. only if required by a concrete consumer, introduce one reusable minimal
   varying-`HFiber` owner rather than a weak-kernel-specific square calculus.

### Selected computational weak kernel

The primary formal package should retain:

```text
ComputationalWeakKernel(C,S,alpha)
  = Sigma K,
    Sigma kappa : Hom(K,A),
      Sigma annihilation : alpha o kappa = 0,
        factorization operation and its reconstruction law.
```

At minimum, for every `T` it supplies a function

```text
factor_T : Ann_alpha(T) -> Hom(T,K)
```

and a path

```text
kappa o factor_T(tau,p) = tau.
```

The owner audit must also account for reindexing/higher action in `T`. A
stable point operation is acceptable only when its whole source action is
retained elsewhere and explicitly documented. No uniqueness path is required
or desired.

The proposition-valued ordinary notion should be derived by `(-1)`-truncating
selected computational data or factor fibres. It is not the primary runtime
interface.

### Whole category capability

After the per-arrow package is stable, define a whole selector over arrows,
approximately:

```text
HasComputationalWeakKernels(C,S)
  := Pi A B, Pi alpha : Hom(A,B), ComputationalWeakKernel(C,S,alpha).
```

Whether this is represented as a transparent dependent function, a stable
classifier with projections, or an arrow-indexed whole family is decided by
owner-position probing. Generic identity/composition remain their current
runtime owners. Do not add a global generic composition rewrite.

## Native Polynomial Weak-Kernel Algorithm

Let `F : R^m -> R^n` be a column matrix over a polynomial ring whose
coefficient domain is operationally a field.

### Original-column syzygy computation

Construct the submodule generated by the ordered columns of `F` and compute a
Gröbner basis with transformation rows. Generate syzygies in the original
free module `R^m` from both:

1. Schreyer S-pair syzygies of the Gröbner basis, multiplied through the
   retained transformation rows; and
2. for every original column `F_j`, the relation

   ```text
   e_j - sum_i q_(i,j) T_i,
   ```

   where division expresses `F_j` in the Gröbner basis and `T_i` is the
   original-column transformation row for basis element `i`.

This second family is essential for zero/redundant original columns and for
recovering all relations among the original generators.

Compute a deterministic Gröbner basis of the resulting syzygy submodule. If
its ordered generators are the columns of `K : R^k -> R^m`, check directly:

```text
F o K = 0.
```

### Reusable lift operation

For `H : R^l -> R^m` with `F o H = 0`, reduce every column of `H` against the
selected syzygy basis. Reject a nonzero remainder. Assemble the coefficient
columns into `U : R^l -> R^k` and check:

```text
K o U = H.
```

The returned data retains each membership result, coefficients, remainder,
progress, and reduction counts. It does not merely return a Boolean.

### Implemented whole weak-kernel and lift result

`src/v3_2/algebra_polynomial_weak_kernel.ts` now constructs a genuine
finite-free weak kernel from the complete original-column syzygy result. Its
selected object has one basis vector per final syzygy generator; its morphism
uses those generators as columns into the original source; and the composed
annihilation matrix is computed and required to be zero before the immutable
record is returned. The record explicitly states that lifts are not claimed
unique.

`algebraPolynomialWeakKernelFactor` accepts a test map only when its target is
the source of the selected map and the computed composite is zero. It divides
each test column by the exact selected syzygy Gröbner basis, retains every
quotient/remainder and progress event, assembles the quotient columns into the
lift matrix, and requires the reconstructed composite to equal the original
test map. Invalid limits, cancellation, foreign endpoints, non-annihilated
tests, nonzero remainders, or failed reconstruction are distinct fail-closed
boundaries.

The new focused suite checks a nontrivial two-column factorization, zero-map
and identity-map weak kernels, a rank-zero source, non-annihilated and foreign
tests, invalid bounds, cancellation, field-only availability, exact zero
remainders, immutability, and nonuniqueness metadata. Root typechecking,
affected lint, and the combined module/weak-kernel `13/13` suite pass.

### Determinism and resource bounds

Preserve the current module-engine conventions:

- stable original-column order;
- deterministic term-order sorting and duplicate removal;
- explicit maximum basis/pair/reduction limits;
- cancellation and progress callbacks;
- no ambient process or filesystem dependency in the native algorithm;
- fail-closed foreign-ring/module/endpoint checks; and
- canonical serializable output suitable for compiler graphs and formal
  reification.

Required operational boundaries include:

- zero maps, including zero source and zero target ranks;
- identity maps;
- injective maps with rank-zero weak kernel;
- redundant and literal zero columns;
- a nontrivial polynomial relation with more than one generator;
- multi-column test maps requiring nontrivial lifts;
- a test map not annihilated by `F`;
- foreign polynomial rings/modules;
- non-field coefficient domains; and
- cancellation/resource exhaustion.

## CAP/homalg-Compatible Operation Architecture

CAP treats a universal construction as an operation family rather than one
undifferentiated flag. Its kernel doctrine separates object, embedding, and
lift operations. Emdash should use the same successful abstraction while
retaining one whole computation as the source of derived observations.

The selected category operation surface should include:

```text
weak-kernel                  : alpha |-> whole record
weak-kernel-object           : derived projection
weak-kernel-morphism         : derived projection
weak-kernel-lift             : alpha,test |-> selected lift
```

The whole operation should be primitive for the polynomial provider; the
object/morphism operations should normally be derived category methods so the
algorithm is not recomputed. `weak-kernel-lift` may reuse the retained syzygy
membership basis.

Add a capability/doctrine layer such as
`additive-category-with-computational-weak-kernels`, parented by
`additive-category`, only after all required roles plan successfully. It must
not imply `preabelian-category` or `abelian-category` yet.

Every category operation receives:

- a backend-neutral algebra operation;
- TypeScript reference implementation;
- categorical-program lowering;
- deterministic runtime schema; and
- focused direct and compiled-graph consumers.

### Implemented finite-free category and capability result

`src/v3_2/algebra_polynomial_weak_kernel_category.ts` now supplies the missing
operational finite-free polynomial category. Objects are polynomial free
modules and arrows are column maps with their existing identity, composition,
and equality. Zero/addition/negation, rank-zero object, binary direct sum with
all four biproduct maps, and block-diagonal arrow action make the facade
operationally additive rather than merely labelling it so.

The doctrine registry now contains the dual pair
`additive-category-with-computational-weak-kernels` and
`additive-category-with-computational-weak-cokernels`. The latter is metadata
only in this goal; no weak-cokernel provider is claimed. The polynomial
finite-free model qualifies the weak-kernel doctrine through all five
inherited additive roles and four new roles.

One primitive whole `weak-kernel` method owns the syzygy computation. Derived
`weak-kernel-object` and `weak-kernel-morphism` methods call that owner, while
`weak-kernel-lift` requests the whole result and invokes the retained
factorization basis. Every category operation has a backend-neutral algebra
operation, reference implementation, compiler lowering, schema, and direct
consumer. Whole weak-kernel and lift categorical programs both compile and
execute through the TypeScript reference engine. The tower ends at the
computational-weak-kernel doctrine and explicitly does not reach pre-Abelian
or Abelian structure.

Focused reviewers cover qualification, every additive operation, biproduct
beta and diagonal identity, derived owner/prerequisite planning, selected
lifts, whole and lift graph execution, direct-sum identity/composition, and
the non-self-dual doctrine metadata. Workspace validation, root typechecking,
affected lint, diff hygiene, and the combined doctrine/module/weak-kernel/
category suite pass `22/22`.

The one required shared `check:ts` boundary run passed workspace validation,
root typechecking, and full lint. Its consolidated suite reached completion
and retained only the inherited active-kernel/article digest and source-line
position failures already recorded at the additive baseline. No failure names
the new module, weak-kernel, doctrine, category, compiler graph, or focused
reviewer files. Those orthogonal pins are evidence, not part of this goal's
mutation scope, and the long aggregate is not repeated for unchanged rows.

This architecture subsumes the CAP/homalg division:

```text
generic categorical algorithms and doctrine roles
  -> category-operation planner/compiler
  -> selected syzygy provider
  -> native TypeScript now; Singular/Oscar/homalg providers later.
```

Emdash additionally connects the same operation to explicit Core/Lambdapi
semantics rather than maintaining an unrelated formalization.

## Singular Differential Oracle

Singular is installed and is an optional, shell-free differential oracle. Add
a deterministic script builder and injected transport for module `syz`
comparison. The oracle should compare:

- both returned matrices annihilate `F`;
- native generators lie in the Singular syzygy span;
- Singular generators lie in the native span; and
- selected test lifts reconstruct.

Do not require literal generator-list equality: different Gröbner conventions
may choose different bases of the same syzygy module. Retain disagreements as
diagnostics; never overwrite native output. Real process execution remains
opt-in and separately tested from pure script construction.

### Implemented Singular differential result

`src/v3_2/algebra_polynomial_weak_kernel_singular.ts` now builds a pure
deterministic Singular program for the selected native weak kernel. Singular
computes `syz(F)` while the script installs the native generator matrix `N`;
it reduces every native generator against `std(syz(F))` and every oracle
generator against `std(N)`. The comparison therefore tests equality of the
generated submodules in both directions rather than literal basis text.

The adapter parses only stable integer markers for both inclusions and the
oracle generator count. It returns immutable agreement/disagreement data and
never replaces the native result. Process requests are shell-free, bounded to
30 seconds and one megabyte of output, and use the injected transport. Source-
rank-zero and target-rank-zero cases have deterministic direct scripts instead
of invalid empty Singular vectors.

Focused tests cover agreement, one-sided disagreement, deterministic script
shape, bounded process requests, malformed/failed output, and both rank-zero
boundaries. The optional real-process test passes against installed Singular
4.3.2 for a nontrivial three-column polynomial matrix. The ordinary suite
passes `5` active tests with one intentional skip; the real gate passes `6/6`.
The adapter remains internal to the weak-kernel model until the final public-
surface audit, avoiding another shared aggregate at this isolated oracle row.

## Computational-To-Formal Bridge

The active formal polynomial layer is universal-property based rather than a
literal polynomial CAS evaluator. Therefore this goal must not fabricate a
definitional ring-wide weak-kernel instance for arbitrary `CommRing`.

Use the existing proof–CAS/declaration artifact architecture:

1. reify the selected finite-free objects and matrices;
2. construct the generic `ComputationalWeakKernel` target;
3. emit the concrete `K` and `kappa`;
4. emit/check or explicitly trust `F o K = 0` under the existing adoption
   classification; and
5. for every requested named test cone, emit `U` and `K o U = H`.

The useful bridge is provider-driven and on demand. A whole ring-wide formal
selector may be introduced only as an explicit capability assumption whose
observations route to generated computational data. A finite list of checked
examples is not evidence for universal availability.

Proof certificates are optional metadata. The acceptance boundary is that the
proof assistant can request, name, consume, and compute with the same weak-
kernel data and factorization operations as the CAS layer.

## Why The Abelian Theorem Is A Later Goal

The next theorem layer must use computational weak kernels of the base
additive category to construct actual kernel object/embedding/lift operations
inside its Freyd category, expose cokernels supplied by the Freyd
construction, and prove the remaining Abelian properties.

Combining that theorem with the algorithm in this goal would obscure two
independent questions:

- whether original-column syzygies and lifts compute correctly; and
- whether the generic Freyd construction turns the capability into Abelian
  structure.

This goal ends before `kernel`, `cokernel`, `image`, `coimage`, exactness, or
homology roles are registered on the Freyd category.

## Deliberate Non-Goals

This goal does not include:

- an unconditional weak-kernel capability for arbitrary `CommRing`;
- the generic weak-kernel-to-Abelian theorem;
- an `AbelianCategory` Lambdapi instance;
- direct Freyd kernel/cokernel/image/coimage operations;
- exact sequences, homology, derived categories, or spectral sequences;
- a proof of Hilbert's basis theorem or formal Gröbner correctness;
- reliance on Singular for native correctness or ordinary execution;
- arbitrary coherent-ring backends beyond the provider interface;
- a parallel matrix, category, cone, or equality grammar;
- generic `Groupoidify` source functoriality/adjunction;
- path-cubical/global-strictness integration; or
- main-branch integration, push, publication, or release.

## Feasibility And Rejection Signals

The goal is strongly feasible because:

- the polynomial module Gröbner engine already retains transformation rows;
- Schreyer S-pair relations and module membership coefficients are active;
- finite-free matrices, zero, composition, and equation reification are
  available;
- the categorical operation planner, compiler lowerings, and TypeScript
  reference engine already support the additive Freyd model;
- `HFiber`, Hom action, preadditive zero, and truncation are active formally;
- proof–CAS delegation and deterministic declaration emission are active; and
- Singular is installed for differential comparison.

Refine or reject a candidate when it:

- generates syzygies only for reduced basis vectors rather than original
  columns;
- cannot reconstruct arbitrary annihilated test columns;
- silently assumes uniqueness of lifts;
- treats a Boolean zero test as factorization data;
- uses a hand-written commuting-square/triangle field instead of the Hom
  fibre;
- erases whole test-object action without a recorded owner;
- requires a global `comp_fapp0` or identity rewrite;
- claims all `CommRing` instances from a field-only algorithm;
- promotes a capability or Abelian doctrine before role qualification;
- lets a Singular disagreement replace native data; or
- requires opaque equality constants where constructed/reified equations are
  available.

Warnings alone are not a rejection signal. Classify overlaps, test both
reduction orders, and distinguish exact import-union warnings from local rule
families.

## Proposed Implementation Sequence

1. Audit the exact original-column syzygy and formal Hom-fibre owner boundary.
2. Implement deterministic original-column syzygy generation.
3. Implement retained weak-kernel data and arbitrary test-map lifts.
4. Register whole/derived category operations and qualify the capability.
5. Add the Singular syzygy differential oracle.
6. Implement the generic internal weak-kernel classifier and factorization
   surface with retained action.
7. Add computation-to-formal selected matrix/lift consumers.
8. Synchronize authorities, catalog/health, warnings, final validation, and
   the successor boundary.

The formal interface may move before the operational operation row when its
owner audit is independent. The native lift computation remains the first
genuine capability consumer and must not be deferred behind documentation.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `WKH-PLAN-0` | complete; checkpoint `3d18fa9` | additive baseline `c4baf61` | living plan, isolated branch/worktree, explicit scope/Git boundary, baseline evidence, persistent goal |
| `WKH-AUDIT-1` | complete; checkpoint `3d18fa9` | plan | metadata-stub, original-column syzygy, lift, formal `HFiber`, operation/doctrine, and Singular owner audit with rejection signals |
| `WKH-SYZYGY-2` | complete; checkpoint `b4b8de6` | module Gröbner transformations | deterministic complete syzygy generators in the original source free module, reconstruction equations, boundaries and focused tests |
| `WKH-LIFT-3` | complete; combined lift/category checkpoint pending | original-column syzygies + membership | whole weak-kernel result and arbitrary annihilated-map factorization with retained coefficients/remainders/progress |
| `WKH-CATEGORY-4` | complete; checkpoint pending | category/engine/doctrine registries | whole primitive plus derived object/morphism/lift operations, compiler lowerings, reference execution, capability qualification |
| `WKH-SINGULAR-5` | complete; checkpoint pending | injected/real Singular transports | pure `syz` script, span comparison, retained disagreements, optional real differential checks |
| `WKH-FORMAL-6` | ready after owner probe | `HFiber`, Hom action, preadditive/additive owners | internal annihilator family, selected computational weak-kernel package, factorization law, proposition view, retained action and reviewers |
| `WKH-BRIDGE-7` | blocked by native and formal rows | proof–CAS/declaration reification | concrete selected matrices, annihilation and lift equations usable through the formal interface without a global arbitrary-ring claim |
| `WKH-CLOSE-8` | blocked by accepted/deferred rows | all rows | standing docs, warnings/LHS, catalog/health, focused/static/integration gates, exact checkpoints and next theorem boundary |

Rows may be split or reordered when dependencies permit. A row may be rejected
or deferred only with durable evidence and a concrete replacement/prerequisite;
difficulty or warning count alone is insufficient.

## Initial Decisions

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-WKH-001` | accepted | Weak kernels are implemented first in the additive finite-free base of the Freyd construction; the generic Freyd-to-Abelian theorem is the next separate goal. |
| `D-WKH-002` | accepted | The primary notion is computational: object, arrow, annihilation, selected lift, and reconstruction, with no uniqueness requirement. |
| `D-WKH-003` | accepted | Annihilated test maps are internal `HFiber` data of existing postcomposition at zero, not hand-written cone squares. |
| `D-WKH-004` | accepted | The native algorithm must compute syzygies of the original ordered matrix columns; Schreyer relations among only Gröbner-basis vectors are insufficient. |
| `D-WKH-005` | accepted | Lift computation is part of the capability, not a later Boolean theorem: membership coefficients assemble the factor matrix and reconstruction is checked. |
| `D-WKH-006` | accepted | Polynomial rings over operational fields are the first provider. Arbitrary rings remain behind an explicit computational-syzygy/coherence capability. |
| `D-WKH-007` | accepted | One whole weak-kernel category operation owns computation; object/morphism observations are derived, following the CAP object/embedding/lift separation without recomputation. |
| `D-WKH-008` | accepted | Singular is a differential oracle only; compare generated submodules bidirectionally rather than demanding literal basis equality. |
| `D-WKH-009` | accepted | The computation-to-formal bridge is on-demand and assumption-explicit where necessary; finite examples do not create a universal ring-wide instance. |
| `D-WKH-010` | accepted | No kernel/cokernel/Abelian doctrine promotion occurs in this goal. |
| `D-WKH-011` | accepted | Generic identity/composition and existing Hom action remain runtime owners; new rules/unifiers require owner-position probes and narrow discriminators. |
| `D-WKH-012` | accepted | Orthogonal strictness/cubical histories, historical main, print/release work, and broad aggregates remain out of scope. |
| `D-WKH-013` | accepted after original-column probes | The selected syzygy carrier is the base `term-over-position` free module indexed by every original column, including zero columns. Pulled-back Schreyer relations plus one rewrite per original generator form the raw generating family; the final Gröbner basis is selected only after every raw and final relation reconstructs zero. |
| `D-WKH-014` | accepted after lift probes | The weak-kernel morphism uses the final syzygy Gröbner-basis vectors as columns. Test lifts use direct division quotients against that same basis rather than transformed membership coefficients for the raw generating family; this keeps the lift source rank aligned with the selected weak-kernel object. |
| `D-WKH-015` | accepted after category probes | TypeScript needed a genuine finite-free polynomial category facade before weak-kernel qualification. It is constructed as an additive category first, then extended by one whole weak-kernel operation and derived observations. Weak kernels and weak cokernels are dual doctrine descriptors, but only the field-polynomial weak-kernel side has an implementation in this goal. |
| `D-WKH-016` | accepted after Singular probes | Differential comparison is bidirectional submodule membership between `syz(F)` and the native generator module, not literal basis equality. Rank-zero cases use direct mathematically forced scripts; disagreements remain non-authoritative observations. |

## Validation Matrix

For each TypeScript semantic tranche:

- focused module/provider tests including positive and fail-closed boundaries;
- root typecheck and affected-file lint;
- workspace check when schemas/exports/setup are affected;
- deterministic serialization/replay where artifacts are introduced;
- direct category-operation planning/execution;
- compiled categorical-program execution through the reference engine;
- one complete `check:ts` only at an actually shared TypeScript integration
  boundary, carrying forward known unrelated source-pin evidence otherwise;
- exact staged diff and plan ledger before checkpoint.

For each Lambdapi semantic tranche:

- smallest owner-position probe;
- positive typed consumer and wrong-endpoint/noncollapse consumer;
- whole/higher-action accounting;
- bounded quiet source and reviewer checks;
- warning-enabled exact predecessor/import-union comparison;
- strict inferred-slot LHS audit;
- registration in maintained source/check inventories;
- catalog and proportional health/source snapshot refresh;
- source TOC/reference/header/diff gates at closeout;
- no unbounded Lambdapi invocation and a 90-second maximum per target.

Real Singular tests are optional/environment-gated. Pure script building and
injected transport tests are mandatory. Do not run print, book, release, or
unrelated repository aggregates.

## Sources And Design References

- Sebastian Posur, *A Constructive Approach to Freyd Categories*, especially
  the computational weak-kernel definition and constructive Freyd theorem:
  <https://link.springer.com/article/10.1007/s10485-020-09612-y>.
- CAP doctrine overview, including object/embedding/lift operation families:
  <https://homalg-project.github.io/docs/CAP_project-based/>.
- CAP kernel operation manual:
  <https://homalg-project.github.io/CAP_project/CAP/doc/chap6.html>.
- FreydCategoriesForCAP documentation:
  <https://homalg-project.github.io/CAP_project/FreydCategoriesForCAP/>.

These are design references, not repository authority. Active source and the
repository SOP determine implementation truth.

## Persistent Goal Launch Prompt

Continue `TS-EMDASH-FREYD-COMPUTATIONAL-WEAK-KERNELS` from the living plan in
`docs/TYPESCRIPT_EMDASH_FREYD_COMPUTATIONAL_WEAK_KERNELS_PLAN.md`. Treat active
source and the root/nested SOP as authority. Work only in
`/home/user1/emdash1-freyd-weak-kernels-v1` on branch
`goal/freyd-computational-weak-kernels-v3.2`, preserving baseline
`c4baf61102d4dc27b68406fdc3536c82bf01896c` as comparison evidence. Resume the
first dependency-ready ledger row and revise the plan whenever probes refine
the architecture. Preserve original-column syzygies, selected nonunique
factorization, Hom-fibre internalization, whole action, backend-neutral
category operations, provider capability indexing, Singular-as-oracle status,
generic id/composition ownership, owner-position probing, warning
classification, strict LHS audits, and proportional validation. Local
validated checkpoint commits are authorized after coherent bounded tranches
are green and the exact staged diff plus ledger are synchronized. Do not push,
merge, publish, release, create a PR, amend, rebase, reset, rewrite history,
delete a branch, or remove a worktree. Do not integrate orthogonal path-
cubical/global-strictness work. Do not claim kernels, cokernels, Abelian
structure, exactness, or homology. The goal is complete only when every scoped
row is implemented, rejected with durable evidence, or explicitly deferred
behind a concrete prerequisite, and all affected authorities are synchronized.
