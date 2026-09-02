# TypeScript/emdash Constructive Freyd Abelian Computation Plan

Date: 2026-09-02

Plan-ID: `TS-EMDASH-FREYD-ABELIAN-COMPUTATION`

Status: active on a dedicated branch/worktree

Baseline: `7c537a6be46f25fc847664786710357c33fc623e`

Branch: `goal/freyd-abelian-computation-v3.2`

Worktree: `/home/user1/emdash1-freyd-abelian-v1`

Decision-Response-Evidence:

- `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a06093-98f1-7651-91b5-b5b94a5d8809`

## Purpose

This plan is the constructive successor to the completed Freyd pre-Abelian
development. It adds the remaining computational normality operations,
derives image and coimage calculus, constructs the coimage–image comparison
isomorphism, and qualifies the polynomial Freyd provider as an operational
Abelian category.

The intended dependency chain is:

```text
computational pre-Abelian Freyd category
  -> lifts along monomorphisms
  -> colifts along epimorphisms
  -> images and coimages
  -> coimage-image comparison isomorphism
  -> operational AbelianCategory.
```

This is the direct completion of Sebastian Posur's constructive proof of
Freyd's theorem:

```text
A(P) is Abelian  <=>  P has weak kernels.
```

The completed baseline already proves and computes the forward construction
through genuine Freyd kernels and cokernels. The remaining constructive data
are precisely lifts along monomorphisms and colifts along epimorphisms, from
which the normal image/coimage factorization follows.

The published article numbers these operations as Constructions **3.14** and
**3.15**. Earlier plan prose that called them Constructions 3.13 and 3.14 used
an older/off-by-one numbering and is not authority for this goal.

## Operational And Git Boundary

Before this branch was created, the clean historical `main` worktree was
fast-forwarded from `c781a42` to the completed pre-Abelian head `7c537a6b`.
The ancestry check reported zero commits unique to `main` and fifteen commits
on the completed branch. No path-cubical, global-strictness, or other
orthogonal branch was integrated.

The user explicitly authorized this living plan, dedicated branch/worktree,
the preceding reviewed fast-forward, persistent goal continuation, and local
validated checkpoint commits following the repository Git SOP. This does not
authorize push, publication, release, PR creation, merge beyond that completed
fast-forward, rebase, amend, reset, history rewriting, branch deletion, or
worktree removal.

The baseline contains:

- generic internal computational kernels and cokernels formulated by
  contractible `HFiber` factor spaces;
- formal finite-free and Freyd `AdditiveCategory` structures;
- computational weak pullbacks derived from weak kernels;
- native polynomial Freyd kernels/cokernels, lifts/colifts, reconstruction,
  and quotient uniqueness;
- complete kernel/cokernel category-operation role families;
- an operational polynomial Freyd provider qualified as
  `preabelian-category`;
- capability-parameterized formal witnessed kernel/cokernel families;
- `CommRingFreydWitnessedPreAbelian` without a fabricated quotient decoder;
  and
- selected proof–CAS replay of all four pre-Abelian operations through eight
  checked matrix equations.

## Reviewed Mathematical Boundary

### Constructive Abelian data are lift and colift algorithms

For a pre-Abelian category, monicity can be characterized by the selected
kernel embedding being zero; epicity is characterized dually by the selected
cokernel projection being zero. Posur's constructive definition of an Abelian
category then asks for:

```text
lift along every monomorphism;
colift along every epimorphism.
```

These operations are more fundamental computational data than merely naming
image and coimage objects. The current TypeScript `ABELIAN_DOCTRINE` asks only
for `image`, `coimage`, and `coimage-image-isomorphism`; this goal must
strengthen that interface so end users can request the actual normality
operations and all derived observations.

### Witnesses are inputs, not hidden propositions

The published construction explicitly treats monicity/epicity and
zero-composite witnesses as algorithm input. This matches the active formal
Freyd representation:

- a raw presentation morphism retains its relation witness;
- a raw agreement retains the target-factorization matrix;
- the native polynomial congruence solver computes such witnesses; and
- every explicit agreement maps to a path in the set-truncated Freyd Hom.

Thus quotient effectiveness is **not** a prerequisite for the normality
algorithms. The goal should continue with witness-enriched operations while
preserving the stronger closed formal package as a separate gate.

### Closed quotient effectiveness remains separately gated

The active formal quotient maps raw agreements to truncated-Hom paths but does
not decode an arbitrary path back into a raw agreement. A closed concrete
formal `PreAbelianCategory`, and therefore a closed concrete formal
`AbelianCategory`, cannot be claimed merely from finitely many generated
equations.

This goal contains an early bounded effectiveness audit. That audit may
discover a valid quotient eliminator that constructs the required factor
directly without choosing a raw witness. It is not permitted to introduce
choice, an opaque equality bridge, or an unproved decoder. Failure to find such
an eliminator does not block the witnessed normality construction.

The expected formal completion boundary is therefore:

```text
generic internal ComputationalAbelianCategory;
operational polynomial Freyd AbelianCategory;
CommRingFreydWitnessedAbelian(R,W);
closed formal CommRingFreyd AbelianCategory only if effectiveness is proved.
```

## Generic Internal Formulation

### Monomorphisms and epimorphisms

For `m : A -> B`, define monicity by cancellation on every incoming Hom:

```text
IsMonic(m)
  := forall T u v,
       m o u = m o v -> u = v.
```

Dually:

```text
IsEpic(e)
  := forall T u v,
       u o e = v o e -> u = v.
```

These are properties of existing Hom actions, not new arrow grammars. When a
selected computational kernel/cokernel is available, prove the standard
characterizations:

```text
IsMonic(m)  <->  kernel_embedding(m) = 0;
IsEpic(e)   <->  cokernel_projection(e) = 0.
```

The direction actually needed by a construction may be implemented first;
the plan must record any deferred converse rather than silently assuming it.

### Normal-monomorphism test and lift space

Let `m : A -> B`, let `q : B -> Q` be its selected cokernel projection, and
let a test consist of `tau : T -> B` with `q o tau = 0`. Reuse the existing
cokernel-annihilator fibre for the test. The lift classifier is:

```text
NormalMonoLiftSpace(m,tau)
  := HFiber(
       Hom(T,A) --(m o -)--> Hom(T,B),
       tau).
```

For a monomorphism, this factor space is a proposition by cancellation. A
computational normal-monomorphism operation selects its centre and proves it
contractible for every cokernel-annihilated test. Readable projections expose:

```text
lift_along_monomorphism;
lift_along_monomorphism_reconstruction;
lift_along_monomorphism_uniqueness.
```

### Normal-epimorphism test and colift space

Dually, for `e : A -> B`, selected kernel embedding `k : K -> A`, and a test
`tau : A -> T` with `tau o k = 0`:

```text
NormalEpiColiftSpace(e,tau)
  := HFiber(
       Hom(B,T) --(- o e)--> Hom(A,T),
       tau).
```

Contractibility gives the selected colift, reconstruction, and uniqueness.
No semantic record containing a manually written commuting square is allowed.

### Generic computational Abelian package

Define whole capabilities over one existing `PreAbelianCategory`:

```text
HasLiftsAlongMonomorphisms(C,P);
HasColiftsAlongEpimorphisms(C,P);

ComputationalAbelianCategory(C)
  := PreAbelianCategory(C)
     + HasLiftsAlongMonomorphisms(C,...)
     + HasColiftsAlongEpimorphisms(C,...).
```

The exact record layout must project the already selected additive,
kernel/cokernel, and normality structures rather than duplicating them.

## Derived Image And Coimage Calculus

Images and coimages are derived from selected kernels and cokernels:

```text
Im(f)   := Ker(Coker(f));
Coim(f) := Coker(Ker(f)).
```

Expose whole results and readable observations:

```text
image;
image-object;
image-embedding;
coastriction-to-image;

coimage;
coimage-object;
coimage-projection;
astriction-from-coimage.
```

Use the existing universal properties to construct the comparison:

```text
A --p_f--> Coim(f) --chi_f--> Im(f) --i_f--> B

f = i_f o chi_f o p_f.
```

This comparison exists in every selected pre-Abelian category. Normality then
constructs an inverse and the two inverse laws, packaged through the existing
`IsoEvidence`/omega-equivalence owner appropriate to the ordinary Hom level.
Do not postulate a primitive isomorphism or a separate image algorithm.

## Concrete Freyd Algorithms

### Monomorphism witness

For a raw Freyd morphism `alpha : P -> Q`, compute its selected Freyd kernel.
A constructive monomorphism witness is the explicit presentation agreement:

```text
kernel_embedding(alpha) ~ 0.
```

The native provider may return a classified success/failure result because
its quotient congruence solver is effective. The formal witnessed operation
takes the successful raw agreement as data.

### Construction 3.14: lift along a monomorphism

For monic `alpha : P -> Q` and test `tau : T -> Q`, compute the selected
cokernel of `alpha`. The input includes an agreement witnessing:

```text
cokernel_projection(alpha) o tau ~ 0.
```

Its agreement matrix has the block form corresponding to the enlarged
cokernel relation matrix `[R_Q, alpha]`:

```text
[tau_RQ, tau_A].
```

The second component `tau_A` is the morphism datum of the desired lift. The
relation witness is built from:

- the test's existing relation witness;
- the two block components of the zero agreement;
- the monomorphism's kernel-zero witness; and
- the existing weak-pullback factor operation.

Correctness must retain the explicit relation equation, quotient
reconstruction `alpha o lift = tau`, and quotient uniqueness.

### Epimorphism witness

Dually, an epimorphism witness for `alpha` is the explicit agreement:

```text
cokernel_projection(alpha) ~ 0.
```

Its block witness decomposes as `[sigma_RQ, sigma_A]` and satisfies the
identity decomposition underlying the published Construction 3.15.

### Construction 3.15: colift along an epimorphism

For epic `alpha : P -> Q` and a test `tau : P -> T` annihilating the selected
kernel embedding, use the epic witness component `sigma_A` to construct the
colift datum. The relation witness and reconstruction agreement must follow
the published equations and the existing two weak-pullback kernel data.

The CAP source is implementation evidence for operation orientation, not
authority over active emdash column conventions. Recover every block
orientation against the current native and formal matrix types before
promotion.

## TypeScript Category/CAS Surface

### Complete operation families

Strengthen `ABELIAN_DOCTRINE`. At minimum, its usable role family should
include:

```text
monomorphism-witness;
epimorphism-witness;
lift-along-monomorphism;
colift-along-epimorphism;

image;
image-object;
image-embedding;
coastriction-to-image;

coimage;
coimage-object;
coimage-projection;
astriction-from-coimage;

coimage-image-comparison;
coimage-image-isomorphism.
```

The audit may refine names to match established CAP terminology and emdash
operation conventions. Whole constructions own computation; object,
structural-arrow, factor, and comparison observations are derived methods.

### Compiler and execution requirements

Every public operation must have:

- a runtime schema;
- category-method registration with exact prerequisites;
- backend-neutral algebra-operation lowering;
- a TypeScript reference implementation;
- computation-graph execution; and
- deterministic serialization/comparison.

The polynomial Freyd provider qualifies as `abelian-category` only after all
required roles plan and execute. The field-module implementation remains
differential evidence; its split finite-dimensional linear algebra must not be
used to implement the polynomial Freyd algorithms.

### Normality witnesses and errors

Do not erase witness data into Booleans. A successful classified result must
retain the selected kernel/cokernel, zero morphism, agreement witness, and the
equation it certifies. Negative results remain explicit and must distinguish:

- invalid endpoints;
- non-monic/non-epic input;
- a test that fails the required annihilation equation;
- malformed/foreign-ring data; and
- resource limits.

## Formal Witnessed Abelian Surface

Add rule-free, capability-parameterized formal owners along the lines of:

```text
CommRingFreydWitnessedMonomorphism(R,W,alpha);
CommRingFreydWitnessedEpimorphism(R,W,alpha);
CommRingFreydWitnessedNormalMonoUniversal(R,W,alpha);
CommRingFreydWitnessedNormalEpiUniversal(R,W,alpha);
CommRingFreydWitnessedAbelian(R,W).
```

The exact names may be refined after owner audit. The selected package must:

- project the exact existing `CommRingFreydWitnessedPreAbelian` value;
- quantify over raw presentation morphisms;
- take explicit kernel-zero/cokernel-zero and test-annihilation agreements;
- construct raw lift/colift morphisms and relation witnesses;
- produce quotient reconstruction and uniqueness paths through existing
  agreement-to-path owners; and
- package the image/coimage comparison inverse laws when their raw agreements
  are constructed.

It must not be advertised as the closed generic formal `AbelianCategory`
unless the effectiveness audit actually supplies the missing arbitrary-path
elimination.

## Proof–CAS Bridge

Extend the selected Freyd formal bridge to replay:

```text
monomorphism witness;
lift along monomorphism;
epimorphism witness;
colift along epimorphism;
image/coimage comparison and inverse.
```

Reuse the established formal presentation-morphism and agreement realizations.
Reify at least:

- kernel-embedding-zero and cokernel-projection-zero witness equations;
- lift/colift relation-preservation equations;
- lift/colift reconstruction equations;
- the factorization `f = i_f o chi_f o p_f`; and
- both comparison inverse equations.

Each adapter must replay the actual native operation and compare the exact
selected whole output. Named equations do not create a ring-wide formal
capability.

## No Manual Diagram Fields

Every apparent square or triangle must arise from existing internal data:

- a relation-preserving raw morphism;
- a presentation agreement witness;
- an `HFiber` point/path;
- generic composition/addition/zero paths;
- kernel/cokernel universal data; or
- a whole Hom action.

Do not introduce an independent semantic commutativity record, Boolean law,
or parallel quotient grammar.

## Computation And Rule Policy

- Generic identity, composition, addition, negation, Hom action, kernels, and
  cokernels remain their current owners.
- Prefer transparent semantic definitions and theorem-level paths.
- Add runtime rules only for a genuinely new constructor-visible stable whole
  owner with a measured consumer.
- Use proof-time unification only between suitable rigid heads and normalized
  semantic bodies, with typed `eq_refl` validation.
- Follow inferred-slot SOP; no compound reducible endpoint expressions in
  nondiscriminating LHS positions.
- Warnings are diagnostics, not vetoes; subject-reduction failure, timeout,
  action loss, or unjoinable semantics are rejection signals.
- Never add broad rules for global `id`, `comp_fapp0`, or generic `fapp*`
  merely to expose one Abelian operation.

## Completion Boundary

The goal is complete only when:

- generic monic/epic and normality factor-space definitions check;
- generic selected lift/colift operations expose reconstruction and
  uniqueness;
- image, coimage, comparison, and comparison inverse are derived rather than
  postulated;
- nontrivial polynomial Freyd monic/epic witnesses compute;
- nontrivial lift and colift operations retain all raw agreement data;
- the complete TypeScript operation families lower and execute;
- the polynomial Freyd provider genuinely qualifies as `abelian-category`;
- the formal capability-indexed witnessed Abelian package checks;
- selected proof–CAS consumers replay the actual operations;
- identity, zero, non-monic/non-epic, invalid-test, foreign-ring, limit, and
  deterministic boundaries are covered;
- every new rule/unifier has owner-position, warning, subject-reduction, and
  strict-LHS evidence;
- affected examples, catalog, source-health snapshot, standing authorities,
  focused tests, typecheck, and affected lint are current; and
- every ledger row is implemented, rejected with durable evidence, or
  explicitly deferred behind a concrete prerequisite.

The goal does **not** complete merely because the existing three-role
`ABELIAN_DOCTRINE` happens to qualify or because image/coimage objects can be
named.

## Deliberate Non-Goals

This goal does not include:

- choice or a postulated decoder for arbitrary truncated quotient paths;
- the claim that every abstract `CommRing` supplies effective weak kernels or
  decidable congruence;
- replacing the active Freyd quotient representation;
- exact sequences or exact-category infrastructure;
- homology or cohomology objects;
- projective/injective resolutions beyond existing bounded-free structures;
- derived categories, derived functors, or spectral sequences;
- unrelated cubical/global-strictness integration;
- print/book/release work; or
- push, publication, PR, history rewriting, branch/worktree cleanup.

The recommended successor is the exactness/homology bridge over the newly
qualified Abelian provider, reusing the existing bounded-free-complex and
proof–CAS infrastructure.

## Feasibility And Rejection Signals

The goal is strongly feasible because:

- the native congruence solver already returns exact agreement witnesses;
- formal and native kernel/cokernel presentations expose every block used by
  Posur's formulas;
- finite-family and matrix block constructors/laws are active;
- weak-pullback factors are already computational;
- generic kernel/cokernel uniqueness is already internalized by
  contractibility;
- the field-module model independently exercises lifts/colifts; and
- the category-operation, compiler, graph, proof–CAS, and live Lambdapi
  bridges are active.

Refine or reject a candidate when it:

- represents monicity/epicity only as a Boolean and discards the witness;
- derives the polynomial algorithm from field-only matrix inverses;
- assumes an arbitrary quotient path can be decoded to a raw agreement;
- postulates the coimage–image isomorphism;
- constructs only image/coimage objects without structural arrows and
  factorization;
- qualifies the doctrine without lift/colift usability roles;
- treats a weak-kernel factor as unique;
- duplicates existing universal-construction or quotient grammars;
- introduces manual commuting diagrams;
- caps a whole construction needed by another action; or
- depends on an unrelated aggregate or orthogonal branch.

## Implementation Ledger

| ID | State | Dependencies | Required result |
|---|---|---|---|
| `FAB-PLAN-0` | complete; checkpoint `002f7540` | baseline `7c537a6b` | living plan, isolated branch/worktree, fast-forward evidence, Git/scope boundary, persistent goal |
| `FAB-AUDIT-1` | complete; checkpoint `8fa545c6` | plan | exact formal/native owners, published/CAP formula orientation, role gaps, baseline evidence, rejection signals |
| `FAB-EFFECTIVENESS-2` | complete as audited deferral at checkpoint `8fa545c6` | quotient owners | no current path-to-agreement/direct dependent eliminator; witnessed work proceeds without choice/opaque decoder |
| `FAB-GENERIC-NORMALITY-3` | complete; checkpoint `7d3e7989` | generic pre-Abelian owner | `IsMonic`, `IsEpic`, normal lift/colift spaces, selected capability packages, reconstruction/uniqueness |
| `FAB-GENERIC-IMAGE-4A` | complete through canonical comparison; checkpoint `f277b3d1` | selected kernels/cokernels | derived image/coimage, projection/embedding, comparison, and factorization `f = i o chi o p` |
| `FAB-GENERIC-IMAGE-4B` | blocked on concrete normality/bimorphism route | generic comparison + normality | comparison monic/epic consequences and constructed `IsoEvidence` inverse |
| `FAB-MONO-NATIVE-5A` | complete; checkpoint `852af783` | polynomial Freyd kernels/cokernels | monomorphism witness and Construction 3.14 lift with agreements/reconstruction/uniqueness |
| `FAB-MONO-FORMAL-5B` | active | formal witnessed pre-Abelian | witnessed monomorphism and formal Construction 3.14 |
| `FAB-EPI-NATIVE-6A` | complete; checkpoint `852af783` | polynomial Freyd kernels/cokernels | epimorphism witness and Construction 3.15 colift with agreements/reconstruction/uniqueness |
| `FAB-EPI-FORMAL-6B` | blocked on formal mono helper orientation | formal witnessed pre-Abelian | witnessed epimorphism and formal Construction 3.15 |
| `FAB-IMAGE-NATIVE-7A` | complete; checkpoint `8543cfe9` | native pre-Abelian provider | whole image/coimage/comparison/isomorphism operations and boundaries |
| `FAB-IMAGE-FORMAL-7B` | blocked on formal normality + generic image | formal witnessed normality | witnessed image/coimage comparison and inverse paths |
| `FAB-CATEGORY-8` | complete; checkpoint pending | operation/doctrine engine | strengthened Abelian role family, provider qualification, compiler/reference/graph execution |
| `FAB-FORMAL-9` | blocked on formal image | explicit weak-kernel capability | `CommRingFreydWitnessedAbelian` and readable projections; closed package only if effectiveness succeeds |
| `FAB-BRIDGE-10` | blocked on native/formal operations | proof–CAS bridge | selected exact normality/comparison equations replay actual operations |
| `FAB-DIFFERENTIAL-11` | optional after native operations | stable reference adapters | non-authoritative field-module/CAP/Singular comparison without replacing native data |
| `FAB-CLOSE-12` | blocked on required rows | all required rows | standing docs, warning/LHS/catalog/health evidence, focused gates, exact checkpoints and successor boundary |

Rows may be split or reordered as probes refine dependencies. A row may be
rejected or deferred only with durable evidence and a concrete replacement or
prerequisite.

## Decision Ledger

| ID | State | Decision |
|---|---|---|
| `D-FAB-001` | accepted | The next theorem boundary is constructive Freyd normality culminating in an operational Abelian category. |
| `D-FAB-002` | accepted | Published numbering is Construction 3.14 for mono lifts and Construction 3.15 for epi colifts. |
| `D-FAB-003` | accepted | Quotient effectiveness is audited but does not block witness-enriched normality. |
| `D-FAB-004` | accepted | Monicity/epicity and test annihilation retain explicit agreement witnesses; they are not reduced to Booleans. |
| `D-FAB-005` | accepted | Generic lift/colift universality is contractibility of internal `HFiber` factor spaces. |
| `D-FAB-006` | accepted | Images and coimages are derived as kernel-of-cokernel and cokernel-of-kernel, not primitive algorithms. |
| `D-FAB-007` | accepted | The coimage–image comparison is constructed from existing universal properties; normality constructs its inverse. |
| `D-FAB-008` | accepted | `ABELIAN_DOCTRINE` must expose lift/colift and complete image/coimage usability roles before qualification. |
| `D-FAB-009` | accepted | The concrete formal result remains `CommRingFreydWitnessedAbelian` unless an effective arbitrary-path eliminator is proved. |
| `D-FAB-010` | accepted | Field-module split inverses are differential evidence only; polynomial Freyd algorithms use retained presentation agreements and weak-pullback data. |
| `D-FAB-011` | accepted | Whole operations own computation; observations and role-specific usability methods are derived. |
| `D-FAB-012` | accepted | Exactness and homology begin only after this Abelian boundary is complete. |
| `D-FAB-013` | accepted after owner audit | Kernel contractibility derives monicity of selected kernel embeddings; cokernel contractibility derives epicity of selected cokernel projections. These cancellation theorems are prerequisites for generic image/coimage comparison. |
| `D-FAB-014` | accepted after effectiveness audit | Current truncation/groupoidification eliminators promote point laws into sets but do not decode arbitrary truncated-Hom paths to raw agreements. Closed concrete formal qualification remains gated; no choice or opaque decoder is introduced. |
| `D-FAB-015` | accepted after block-owner audit | Formal row-block splitting and projection/eta laws already exist. Native agreement matrices can be split representation-preservingly by their explicit component arrays; add only a checked helper, not a new matrix representation. |
| `D-FAB-016` | accepted after Construction 3.14 audit | The monic lift datum is the lower block of the test's cokernel-zero agreement. Its relation witness is the monic kernel-zero witness composed with the selected first-weak-pullback factor of the derived relation pair. |
| `D-FAB-017` | accepted after Construction 3.15 audit | The epic colift datum is the test map composed with the lower block of the cokernel-projection-zero witness. Its relation witness uses the test kernel-zero agreement and a selected first-weak-pullback factor; the exact subtraction orientation remains a focused native test question. |
| `D-FAB-018` | accepted after generic normality probe | `IsMonic` and `IsEpic` are direct cancellation types over existing Hom composition. Selected kernel embeddings and cokernel projections satisfy them by constructing one annihilator/coannihilator cone and applying contractibility twice. Normal lift/colift spaces are direct `HFiber`s and the computational Abelian package reuses one existing `PreAbelianCategory`. |
| `D-FAB-019` | accepted after generic image probe | In every selected pre-Abelian category, `Coim(f)` is the selected cokernel of `Ker(f)` and `Im(f)` the selected kernel of `Coker(f)`. Cokernel universality constructs the coastriction, epic cancellation proves it annihilated by `Coker(f)`, kernel universality constructs `chi`, and associativity gives `f = i o chi o p`. Comparison invertibility remains a separate normality theorem. |
| `D-FAB-020` | accepted after native Construction 3.14 tests | Native monicity is classified by the selected kernel embedding's explicit agreement with zero. The lower block of a cokernel-zero test agreement is the lift datum; its expected relation witness is the kernel-zero witness after the selected first-weak-pullback factor. Multiplication by `x` with test `xy` computes lift `y`. |
| `D-FAB-021` | accepted after native Construction 3.15 tests | Native epicity is classified by the selected cokernel projection's explicit agreement with zero. Splitting its identity witness and factoring the pair `sigma_A o R_Q`, `id - sigma_RQ o R_Q` through the first weak pullback constructs the colift relation witness. The quotient projection by `x` computes an identity colift. |
| `D-FAB-022` | accepted after native image tests | One whole native result derives kernel, coimage, cokernel, image, coastriction, comparison, and `f = i o chi o p`. The comparison is independently classified monic and epic; Constructions 3.14 and 3.15 produce two inverse candidates, their agreement, and both quotient inverse laws. No isomorphism is postulated. |
| `D-FAB-023` | accepted after category-provider tests | `ABELIAN_DOCTRINE` requires 14 normality/image roles in addition to inherited pre-Abelian roles. The field-polynomial Freyd provider qualifies only when witness, lift/colift, whole image/coimage, all structural observations, comparison, and isomorphism are plannable and executable. |

## Implemented Generic Normality Layer

`emdash3_2_abelian_categories.lp` now defines direct cancellation properties
`IsMonic` and `IsEpic`, proves every selected computational kernel embedding
monic and every selected computational cokernel projection epic, and packages
the normal lift/colift test and factor spaces as internal `HFiber`s.

`HasLiftsAlongMonomorphisms` and `HasColiftsAlongEpimorphisms` require each
normal factor space to be contractible. Their readable projections expose the
selected lift/colift, reconstruction path, and uniqueness path. The thin
`ComputationalAbelianCategory` pairs those capabilities with one existing
`PreAbelianCategory`; it does not duplicate additive, kernel, or cokernel
data.

The source introduces no rewrite or unification rule. Its owner-position
warning inventory is exactly neutral at
`1,386 = 1,217 critical pairs + 169 replaceable variables` against
`emdash3_2_kernels_cokernels.lp`. The source and focused reviewer pass, and
the strict LHS audit has no clauses attributable to this module. Both files
are registered; the strict catalog remains current and the source-metrics
health snapshot covers 413 files without launching an unrelated aggregate.

## Implemented Generic Image And Coimage Comparison

`emdash3_2_abelian_images.lp` now derives `Coim(f)` as the selected cokernel
of `Ker(f)` and `Im(f)` as the selected kernel of `Coker(f)`. It exposes the
coimage projection, image embedding, coimage-to-target coastriction, canonical
comparison `chi`, the comparison reconstruction, and the complete
factorization `f = i o chi o p`.

The construction uses only existing universal data. Contractibility first
proves every selected cokernel projection epic. That cancellation turns the
annihilation path after the coimage projection into a direct annihilation path
for the coastriction, which is then fed to the selected image kernel. The
module also records the easy normality directions: monic arrows have zero
selected kernel embeddings and epic arrows have zero selected cokernel
projections.

The module is rule-free and passes its source and reviewer checks. Its warning
inventory equals the import owner at
`1,386 = 1,217 critical pairs + 169 replaceable variables`, and the strict LHS
audit has no new clauses. The comparison inverse is intentionally not
postulated; it remains `FAB-GENERIC-IMAGE-4B` and will consume the concrete
normality route. Both files are registered, and the source-metrics health
snapshot now covers 415 files without an unrelated behavioral aggregate.

## Implemented Native Freyd Normality

`algebra_polynomial_freyd_normality.ts` now implements the published
Constructions 3.14 and 3.15 on the active polynomial presentation carrier. A
checked row-block helper splits agreement matrices without introducing a new
matrix representation.

`algebraPolynomialFreydMonomorphismWitness` computes the selected kernel and
retains the agreement between its embedding and zero. For an annihilated test,
the cokernel-zero agreement is split into target-relation and source-generator
blocks; the lower block is the lift map. Its relation witness is constructed
by one existing first-weak-pullback factor followed by the retained
kernel-zero witness. Reconstruction and competing-lift uniqueness are checked
in the Freyd quotient.

Dually, `algebraPolynomialFreydEpimorphismWitness` retains the split identity
decomposition of the selected cokernel projection. The colift datum is the
test composed with the lower block. The pair consisting of that block after
target relations and `id -` the upper block after target relations factors
through the existing first weak pullback; the test kernel-zero witness after
that factor is the expected relation witness. Reconstruction and competing-
colift uniqueness are checked in the quotient.

Eight focused tests cover row splitting, multiplication-by-`x` monicity and
the `xy` lift, the quotient-by-`x` epimorphism and identity colift, identity,
non-monic/non-epic inputs, non-annihilated tests, endpoint rejection,
uniqueness, freezing, and deterministic replay. Together with the affected
kernel/cokernel/provider suites, `21/21` tests pass; root typecheck and affected
lint pass. No field-only inverse or external process is used.

## Implemented Native Image/Coimage Isomorphism

`algebra_polynomial_freyd_images.ts` computes the complete canonical
factorization on the existing presentation carrier. It constructs
`Coker(Ker(f))`, `Ker(Coker(f))`, the coimage-to-target morphism, the
coimage–image comparison, the coastriction to the image, and the factorization
agreement.

The comparison is then passed through the actual normality algorithms. Its
kernel-zero and cokernel-zero agreements classify it monic and epic.
Construction 3.14 lifts the image identity and Construction 3.15 colifts the
coimage identity, producing two inverse candidates. The implementation checks
their quotient agreement and both inverse laws before returning the whole
isomorphism result.

Four focused tests cover multiplication by `x`, a nontrivial `[x,y]` row map,
zero, identity, both inverse constructions, factorization, freezing, and
deterministic replay. All pass without a primitive image algorithm, an opaque
isomorphism witness, or field-only linear algebra.

## Implemented Operational Abelian Category

`algebra_polynomial_freyd_abelian_category.ts` extends the unchanged
pre-Abelian polynomial Freyd carrier. It registers primitive monomorphism and
epimorphism witness operations, derived normal lift/colift operations, and one
primitive whole coimage–image isomorphism. Image, coimage, their objects and
structural arrows, coastriction, astriction, and comparison are derived
category methods.

`ABELIAN_DOCTRINE` now requires all 14 usable roles rather than three opaque
labels. Its dual map exchanges mono/epi, lift/colift, image/coimage,
embedding/projection, and coastriction/astriction while retaining the
comparison/isomorphism roles. The provider adds backend-neutral algebra
operations and lowerings for every role, reference implementations, graph
execution, and an Abelian constructor in the categorical tower.

Four provider tests cover full qualification, every derived observation,
normality execution, whole isomorphism execution, compiler and graph paths,
inherited pre-Abelian methods, and non-field rejection. The affected doctrine,
pre-Abelian, normality, image, and Abelian provider matrix passes `25/25`, with
root typecheck and affected lint green.

## Validation Matrix

Use proportional, bounded checks. Do not run print, book, release, or unrelated
repository aggregates.

### Plan and audit

- exact staged/unstaged diff review;
- `git diff --check`;
- Markdown/link/header/reference hygiene;
- workspace contract;
- nearest focused TypeScript Freyd/pre-Abelian tests;
- bounded checks of the formal kernel/cokernel and witnessed pre-Abelian
  owners.

### TypeScript implementation

- affected focused tests after each coherent slice;
- root typecheck and affected lint;
- explicit positive/negative witness tests;
- whole and derived category-method plans;
- compiler/reference-engine/computation-graph execution;
- deterministic replay;
- one complete shared TypeScript gate only at a genuinely affected integration
  boundary and only if not superseded by already-current evidence plus an
  explicit user scope restriction.

### Lambdapi implementation

- smallest owner-position probe with positive and noncollapse consumers;
- every Lambdapi target bounded to at most 90 seconds;
- quiet and warning-enabled source checks;
- exact import-union warning classification;
- strict inferred-slot/LHS audit;
- focused reviewer examples;
- registered source/check/catalog refresh;
- source-health refresh without restarting unrelated long aggregates; and
- bounded integration only at the coherent semantic boundary.

### External differential

- deterministic injected adapter tests if a new adapter is added;
- external process remains environment-gated and non-authoritative;
- disagreement remains observable;
- native execution never depends on the external CAS.

## Sources And Design References

- Sebastian Posur, *A Constructive Approach to Freyd Categories*, published
  Constructions 3.14 and 3.15, Definition A.8, and Theorem 3.5:
  <https://link.springer.com/article/10.1007/s10485-020-09612-y>.
- Local shallow reference clone, CAP implementation orientation:
  `/tmp/emdash-freyd-reference.hjnXCz/FreydCategoriesForCAP/gap/FreydCategory.gi`.
- Completed pre-Abelian plan:
  `docs/TYPESCRIPT_EMDASH_FREYD_PREABELIAN_COMPUTATION_PLAN.md`.
- Completed pre-Abelian owner audit:
  `docs/TYPESCRIPT_EMDASH_FREYD_PREABELIAN_OWNER_AUDIT.md`.

These references guide formulas and operation decomposition. Active source,
focused diagnostics, and repository SOP remain implementation authority.

## Persistent Goal Launch Prompt

Continue `TS-EMDASH-FREYD-ABELIAN-COMPUTATION` from the living plan in
`docs/TYPESCRIPT_EMDASH_FREYD_ABELIAN_COMPUTATION_PLAN.md`. Treat active source
and the root/nested SOP as authority. Work only in
`/home/user1/emdash1-freyd-abelian-v1` on branch
`goal/freyd-abelian-computation-v3.2`, preserving baseline
`7c537a6be46f25fc847664786710357c33fc623e` as comparison evidence. Resume
the first dependency-ready ledger row and revise the plan whenever probes
refine the architecture. Preserve internal `HFiber` universal properties,
contractible factor spaces, explicit monic/epic and annihilation agreements,
selected weak-kernel nonuniqueness, derived image/coimage computation, whole
operation owners, complete usability roles, backend-neutral lowering,
capability-indexed formal data, generic identity/composition ownership,
owner-position probing, warning classification, strict LHS audits, retained
higher action, and proportional validation. Local validated checkpoint commits
are authorized after coherent bounded tranches are green and the exact staged
diff plus ledger are synchronized. Do not push, merge, publish, release,
create a PR, amend, rebase, reset, rewrite history, delete a branch, or remove
a worktree. Do not integrate orthogonal path-cubical/global-strictness work.
Do not claim a closed concrete formal `AbelianCategory` without an effective
quotient eliminator. Do not begin exactness or homology. The goal is complete
only when every scoped row is implemented, rejected with durable evidence, or
explicitly deferred behind a concrete prerequisite, and all affected
authorities are synchronized.
