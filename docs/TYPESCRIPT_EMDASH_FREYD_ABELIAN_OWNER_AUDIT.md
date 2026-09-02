# TypeScript/emdash Freyd Abelian Owner Audit

Date: 2026-09-02

Status: active implementation audit for
`TS-EMDASH-FREYD-ABELIAN-COMPUTATION`

Baseline: `7c537a6be46f25fc847664786710357c33fc623e`

## Audit Question

Can the completed pre-Abelian Freyd implementation support constructive lifts
along monomorphisms, colifts along epimorphisms, image/coimage comparison, and
operational Abelian qualification without changing the active quotient
carrier or postulating a decoder from truncated paths to raw agreements?

## Conclusion

Yes, at the selected two-level boundary:

```text
generic closed internal Abelian definitions;
native polynomial Freyd operational Abelian provider;
formal capability-indexed witnessed Freyd Abelian package.
```

The native congruence solver already computes the raw agreement witnesses
required by Posur's algorithms. The formal witnessed surface can take the same
agreements as explicit inputs. A closed concrete formal package remains gated,
but that gate does not block normality, images/coimages, or the selected
proof–CAS equations.

No new runtime rewrite or unification rule is indicated by this audit.

## Implemented Consumer Result

The audited proof-CAS boundary is now realized by
`src/v3_2/algebra_formal_freyd_abelian.ts`. It replays the operational Abelian
provider and reifies thirteen exact presentation equations spanning normality,
comparison factorization, explicit comparison bimorphism witnesses, inverse
candidate agreement, and both inverse laws. Canonical serialization compares
the complete selected operation output, while the adapter profile explicitly
denies a ring-wide formal capability, quotient-path decoding, or a primitive
isomorphism. A focused generated Lambdapi probe accepts the complete equation
set.

The optional differential gate reuses the established non-authoritative
Singular weak-kernel span comparison, which is the computational prerequisite
actually consumed by Posur Construction 3.14/3.15. A real run against the
installed `Singular` executable passes all six focused tests. No parallel
Singular-level Abelian category representation was added.

## Baseline Evidence

The new worktree bootstrapped successfully with the shared pnpm store.
Proportional baseline validation passed:

- workspace contract and root TypeScript typecheck;
- `20/20` focused doctrine, polynomial Freyd kernel/cokernel,
  pre-Abelian-provider, and formal-bridge tests, with one expected live probe
  skipped;
- bounded checks of `emdash3_2_kernels_cokernels.lp` and
  `emdash3_2_commutative_algebra_freyd_witnessed_preabelian.lp`; and
- the focused witnessed pre-Abelian reviewer.

All registered worktrees were clean before the reviewed `main` fast-forward
and new worktree creation.

## Published And CAP Orientation

The published Posur article uses:

- Construction 3.14: lifts along monomorphisms;
- Construction 3.15: colifts along epimorphisms;
- Definition A.8: pre-Abelian plus those two algorithms is Abelian; and
- Theorem 3.5: `A(P)` is Abelian iff `P` has weak kernels.

The local shallow `FreydCategoriesForCAP` clone implements the same
orientation in `gap/FreydCategory.gi` near the installation of
`LiftAlongMonomorphism` and `ColiftAlongEpimorphism`. CAP obtains witnesses via
its general `WitnessForBeingCongruentToZero`/`Lift` infrastructure. Emdash's
native polynomial presentation congruence already performs that role while
retaining the witness matrix.

The CAP code is useful formula evidence but does not override the active
emdash column convention. All formulas below are restated in the active
orientation.

## Generic Formal Owners

### Existing universal-construction owner

`emdash3_2_kernels_cokernels.lp` already owns:

```text
CokernelCoannihilator;
KernelFactorSpace;
CokernelFactorSpace;
ComputationalKernel;
ComputationalCokernel;
HasComputationalKernels;
HasComputationalCokernels;
PreAbelianCategory.
```

Kernel and cokernel factor spaces are `HFiber`s and their selected structures
store `IsContr` for every test. Their centre/path/contraction projections
already provide the pattern required for normal-monomorphism and
normal-epimorphism factor spaces.

### Missing generic owners

No active Lambdapi module defines:

```text
IsMonic;
IsEpic;
NormalMonoLiftSpace;
NormalEpiColiftSpace;
HasLiftsAlongMonomorphisms;
HasColiftsAlongEpimorphisms;
ComputationalAbelianCategory;
ComputationalImage;
ComputationalCoimage;
CoimageImageComparison.
```

These belong in one new generic extension after
`emdash3_2_kernels_cokernels.lp`, with image/coimage possibly split into a
second module if the proof boundary becomes large.

### Existing isomorphism owner

`IsoEvidence(C,x,y)` in `emdash3_2.lp` stores a forward arrow, inverse arrow,
and both composition laws. It is the correct ordinary categorical owner for
the coimage–image isomorphism. There is no reason to add a parallel isomorphism
record.

## Generic Image/Coimage Construction

For `f : A -> B` in a selected pre-Abelian category, let:

```text
k_f : Ker(f) -> A;
p_f : A -> Coim(f) := Coker(k_f);
q_f : B -> Coker(f);
i_f : Im(f) := Ker(q_f) -> B.
```

The comparison construction is dependency-ready:

1. `f o k_f = 0`, so cokernel universality of `p_f` gives
   `bar_f : Coim(f) -> B` with `bar_f o p_f = f`.
2. `q_f o bar_f = 0` follows after precomposition with the epic cokernel
   projection `p_f`.
3. Kernel universality of `i_f` gives
   `chi_f : Coim(f) -> Im(f)` with `i_f o chi_f = bar_f`.
4. Hence `i_f o chi_f o p_f = f`.

The generic owner must first prove from contractibility that every selected
kernel embedding is monic and every selected cokernel projection is epic.
Those theorems also provide the cancellation used in step 2.

In the normal category, `chi_f` is both monic and epic. Lifting an identity
along it and/or colifting an identity through it constructs the inverse;
cancellation supplies the second inverse law. Package the result with the
existing `IsoEvidence`.

## Formal Quotient-Effectiveness Audit

### Available forward direction

`comm_ring_freyd_agreement_path` maps a raw presentation agreement into a path
in `CommRingFreydHomSet`. Every formal Freyd construction currently uses this
direction successfully.

### Available eliminators do not decode paths

`trunc_zero_set_path_ind` and its binary/ternary variants promote laws from
point constructors to arbitrary **points** of a 0-truncation when the target is
a set. `groupoidify_set_map_ext` proves equality of maps into a set from their
whole-unit observations. Neither owner takes an arbitrary path between two
truncated points and returns an arrow of the raw agreement category.

No active symbol has type or computational content equivalent to:

```text
(class(f) = class(g)) -> RawAgreement(f,g).
```

Such a decoder would choose from a merely represented path witness and is not
derivable from the current eliminators without additional effectiveness or
choice. A direct quotient-level factor operation might still be possible via a
new dependent eliminator, but no existing owner supplies it and this audit
does not postulate one.

### Decision

`FAB-EFFECTIVENESS-2` is closed as an audited deferral:

```text
agreement -> path is active;
path -> agreement is unavailable;
witnessed normality proceeds;
closed concrete formal qualification remains gated.
```

## Native Polynomial Owners

### Agreement representation

`AlgebraPolynomialPresentationMorphismAgreement` retains:

- left/right maps;
- their difference;
- one membership result per column;
- `agreementWitness` into the target relation module;
- the composed target relation matrix; and
- the checked `agrees` flag.

This is exactly the witness-rich input required by both constructions.

### Block splitting

For the cokernel presentation of `alpha : P -> Q`, the relation matrix is:

```text
[R_Q, F_alpha].
```

An agreement into that target has coefficient rows of size:

```text
relations(Q) + generators(P).
```

The native layer presently lacks a named row-block split for module maps, but
its vectors are explicit component arrays and the split is representation-
preserving. Add one small checked helper rather than a second matrix type.

The formal layer already owns the exact operations and laws:

```text
comm_ring_matrix_take_rows;
comm_ring_matrix_drop_rows;
comm_ring_matrix_vertical_proj_eta_path;
comm_ring_matrix_proj1_vertical_path;
comm_ring_matrix_proj2_vertical_path.
```

Thus no formal block prerequisite is missing.

## Construction 3.14 In Active Column Orientation

Let `alpha : P -> Q` have ambient datum `F : A -> B`, source relation
`R_P : R_P -> A`, and target relation `R_Q : R_Q -> B`.

### Monomorphism witness

Compute `kernel(alpha)`. Its embedding datum is the first weak-pullback
projection:

```text
p_A : K_1 -> A.
```

A monomorphism witness is an agreement between that embedding and zero. Its
witness matrix is:

```text
sigma : K_1 -> R_P
with R_P o sigma = p_A.
```

The native congruence solver can classify success/failure and retain `sigma`.

### Test decomposition

For `tau : T -> Q`, an agreement witnessing

```text
coker_projection(alpha) o tau ~ 0
```

has a vertically split coefficient matrix:

```text
[tau_RQ; tau_A]
```

and satisfies:

```text
R_Q o tau_RQ + F o tau_A = tau.
```

The desired lift datum is `tau_A : T -> A`.

### Relation witness of the lift

Let `R_T` and `rho_tau` be the test source relation and relation witness. The
pair:

```text
tau_A o R_T;
rho_tau - tau_RQ o R_T
```

equalizes `F` and `R_Q`, so it factors through the existing first weak
pullback. Let `lambda : R_T -> K_1` be the selected factor. Then:

```text
sigma o lambda : R_T -> R_P
```

is the expected relation witness of the lift. The ordinary presentation
constructor may compute a judgmentally different membership witness; retain
the expected witness and check the defining equation, as the kernel
implementation already does.

### Reconstruction and uniqueness

The lower block equation gives `F o tau_A ~ tau`; the upper block, with the
active subtraction convention, yields an explicit reconstruction agreement.
Competing lifts are compared by the native congruence solver and the monic
witness/cancellation law. The result must retain the agreement, not only
`true`.

## Construction 3.15 In Active Column Orientation

### Epimorphism witness

The selected cokernel projection of `alpha` has identity datum on `B` and
target relation matrix `[R_Q,F]`. An epimorphism witness is its agreement with
zero, split as:

```text
[sigma_RQ; sigma_A] : B -> R_Q + A
```

with:

```text
R_Q o sigma_RQ + F o sigma_A = id_B.
```

### Desired colift datum

For `tau : P -> T`, define:

```text
u := tau o sigma_A : Q -> T.
```

The test input includes an agreement witnessing that `tau` annihilates the
selected kernel embedding.

### Relation witness of the colift

The pair:

```text
sigma_A o R_Q;
id_RQ - sigma_RQ o R_Q
```

equalizes `F` and `R_Q` and therefore factors through the first weak
pullback `K_1`. Composing that selected factor with the test's kernel-zero
agreement witness yields the expected relation witness for `u`.

The precise sign/order of the second component must be checked against the
native `algebraPolynomialModuleMapSubtract` convention in a focused test
before promotion. This is a bounded orientation question, not an architecture
gap.

### Reconstruction and uniqueness

The epic identity decomposition supplies the quotient reconstruction
`u o alpha ~ tau`. Competing colifts are compared by the explicit epic
witness and native congruence. Again, retain the raw agreement.

## TypeScript Doctrine And Provider Audit

### Current doctrine gap

`ABELIAN_DOCTRINE` currently requires only:

```text
image;
coimage;
coimage-image-isomorphism.
```

No provider qualifies it. The doctrine is therefore safe to strengthen before
its first real consumer.

### Required usable roles

The initial target is the full family recorded in the living plan:

```text
monomorphism-witness;
epimorphism-witness;
lift-along-monomorphism;
colift-along-epimorphism;
image plus object/embedding/coastriction;
coimage plus object/projection/astriction;
comparison and comparison-isomorphism.
```

The audit should preserve one whole owner for each coherent result and derive
observations through the existing category-method planner. Role names may be
adjusted once the exact result interfaces exist.

### Existing execution infrastructure

`algebra_polynomial_freyd_preabelian_category.ts` already supplies:

- field-provider gating;
- whole kernel/cokernel primitives;
- derived object/structural/factor methods;
- algebra-operation lowerings;
- reference implementations;
- graph compilation/execution; and
- doctrine qualification.

The Abelian model should extend this value without changing the presentation
carrier or duplicating inherited operations.

## Proof–CAS Audit

`algebra_formal_freyd_preabelian.ts` already serializes exact whole operation
outputs, replays actual provider operations, and reuses formal
presentation-morphism/agreement equations. The next bridge can reuse the same
generic adapter helper for:

- kernel-embedding-zero agreement;
- cokernel-projection-zero agreement;
- lift/colift relation morphisms;
- reconstruction agreements;
- comparison factorization; and
- inverse agreements.

No new Core owner is indicated. The only likely shared helper is deterministic
serialization for the new whole results.

## Recommended Owner Sequence

1. Add a rule-free generic `emdash3_2_abelian_categories.lp` with
   monic/epic, normal factor spaces, selected capabilities, kernel-monic and
   cokernel-epic theorems, and a thin computational Abelian package.
2. Add a rule-free generic image/coimage module if the comparison proof would
   make the normality owner too large.
3. Implement native monomorphism witness and Construction 3.14.
4. Implement native epimorphism witness and Construction 3.15.
5. Promote their formal witnessed counterparts after native orientation is
   fixed.
6. Derive native/formal image, coimage, comparison, and inverse.
7. Strengthen the doctrine and register the complete operational provider.
8. Extend the proof–CAS bridge.

This sequence lets the native matrix tests settle block orientation before the
larger formal proof is committed, while the generic internal formulation
remains independent and can proceed in parallel in the same goal.

## Rejection Signals

Reject or redesign any candidate that:

- loses raw agreement witnesses;
- calls field-only inverses in the polynomial provider;
- postulates quotient effectiveness;
- postulates the comparison isomorphism;
- adds manual square records;
- gives only objects without structural/factor maps;
- qualifies `abelian-category` without normal lift/colift roles;
- duplicates identity/composition/additive/kernel/cokernel owners;
- introduces broad hot-head runtime rewrites; or
- requires an unrelated aggregate or orthogonal worktree.
