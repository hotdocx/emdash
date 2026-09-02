# TypeScript/emdash Abelian Snake Connecting Computation Plan

Date: 2026-09-02

Plan-ID: `TS-EMDASH-ABELIAN-SNAKE-CONNECTING`

Status: active on a dedicated branch/worktree

Baseline: `4036ef47be6c3f82dcac05c257c98b2201c101d7`

Branch: `goal/abelian-snake-connecting-v3.2`

Worktree: `/home/user1/emdash1-abelian-snake-v1`

Decision-Response-Evidence:

- `/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-23_01a02f686142/responses/0101_2026-09-02T13-34-50Z_01a0624f-ca22-7a30-8448-d470dc86b39c.md`

## Purpose

This plan governs the next computational-and-internal vertical slice shared by
the generic categorical kernel, the polynomial Freyd CAS, the CAP-like
categorical-program compiler, Lambdapi, and the proof–CAS bridge:

**computational genuine fiber products, pushouts, and the Abelian snake-lemma
connecting morphism.**

The completed baseline supplies:

- additive and pre-Abelian categories with selected biproducts, kernels, and
  cokernels;
- constructive lifts along monomorphisms and colifts along epimorphisms;
- an operational polynomial Freyd Abelian category;
- capability-indexed witnessed formal Freyd Abelian operations;
- quotient-aware one-degree and bounded homology, exactness, and functorial
  homology;
- retained categorical programs and deterministic polynomial lowering; and
- proof–CAS consumers that replay selected universal constructions and exact
  equations.

The next missing dependency chain is:

```text
selected biproducts + kernels + cokernels
  → genuine computational fiber products and pushouts
  → pullback stability of epimorphisms
  → pushout stability of monomorphisms
  → CAP-style non-split snake construction
  → polynomial Freyd specialization
  → categorical lowering
  → formal witnessed equations and proof–CAS delegation.
```

This goal deliberately does **not** implement the full long exact homology
sequence. The connecting morphism and its universal-construction trace are the
missing prerequisite. A successor goal can use this result with the completed
bounded homology and exactness owners to assemble the long exact sequence and
prove exactness at each displayed term.

## Preparatory Integration And Git Boundary

Before creating this worktree, clean historical `main` was fast-forwarded from
`4acef747d4b80e92c5c653e0b6635e6817a9c909` to the completed Freyd-homology
head `4036ef47be6c3f82dcac05c257c98b2201c101d7`. The reviewed ancestry was
exactly `0 13`; the homology worktree was clean. No path-cubical,
global-strictness, or other orthogonal branch was integrated.

The user explicitly authorized this plan, dedicated branch/worktree,
persistent goal, implementation continuation, and local validated checkpoint
commits following the repository Git SOP. This does not authorize push,
publication, release, PR creation, any merge beyond the completed preparatory
fast-forward, rebase, amend, reset, history rewriting, branch deletion, or
worktree removal.

The baseline commit remains comparison and backtracking evidence. It is not
permission to discard descendant work.

## Reviewed Architectural Gap

### The existing field connecting map is split-linear, not Abelian-general

`src/v3_2/algebra_homological.ts` already computes a connecting morphism for a
degreewise short exact sequence of finite-dimensional vector-space
presentations. Its crucial first step composes a cycle inclusion with a stored
`projectionSection` of the middle-to-quotient epimorphism.

That is valid for vector spaces, where every short exact sequence splits. It is
not valid for general finitely presented polynomial modules: an epimorphism
need not have a section. Directly porting that implementation into the
polynomial Freyd category would therefore produce a mathematically false
general algorithm.

The field implementation remains useful differential evidence. It must not be
the public owner or a hidden prerequisite of the new construction.

### Existing pullback-named owners do not supply the required object

The repository currently has two different relevant layers:

- `emdash3_2_pullbacks.lp` assumes a coherent contravariant slice
  base-change structure and exposes `Σ_f ⊣ f*`. It does not construct a
  pullback object from selected Abelian kernels.
- `emdash3_2_computational_weak_pullbacks.lp` derives a weak pullback from the
  weak kernel of `[f,-g]`. Its factor operation is intentionally nonunique.

The snake construction requires a genuine universal fiber product: every test
cone must have a contractible factor space. The weak-pullback package is an
important lower-layer precedent for the difference-map orientation and
internal cone carrier, but it is insufficient as the snake owner.

No corresponding computational pushout owner is active at the baseline.

### CAP gives the correct non-split construction

The reviewed CAP tutorial implementation computes a snake morphism from a
composable triple

```text
A ──δ──→ B ──β──→ C ──λ──→ D
```

with the needed zero composite. In CAP terminology its exact algorithm is:

```text
γ       := CokernelColift(δ, λ ∘ β)
ι       := KernelEmbedding(γ)
ε       := CokernelProjection(δ)
μ       := KernelEmbedding(λ)
α       := KernelLift(λ, β ∘ δ)
π       := CokernelProjection(α)

p₁,p₂   := projections of FiberProduct(ι,ε)
q₁,q₂   := injections of Pushout(μ,π)

u       := ColiftAlongEpimorphism(p₁, q₁ ∘ β ∘ p₂)
∂       := LiftAlongMonomorphism(q₂,u).
```

The source file is
`CAP_project/Manual/GAP_tex/vecspaces_example/SnakeLemmaImplementation.tex`
at reviewed CAP commit `d21dc5f5f420829f53cf3e00eef7d971cfa6ea8b`.
Every composition order and endpoint must still be recovered against emdash's
current `after ∘ before` and column-matrix conventions before promotion.

This algorithm uses no chosen splitting. Its computational prerequisites are
exactly the whole operations emdash aims to expose: kernels, cokernels, genuine
fiber products, genuine pushouts, normal-epi colifts, and normal-mono lifts.

## Genuine Computational Fiber Products

Let

```text
f : A → C
g : B → C
```

be a cospan in a selected pre-Abelian category. Form its biproduct difference:

```text
d := [f,−g] : A ⊕ B → C.
```

Select the kernel

```text
k : P → A ⊕ B
```

and define:

```text
p₁ := π₁ ∘ k : P → A
p₂ := π₂ ∘ k : P → B.
```

The kernel annihilation law and biproduct/additive laws derive the
compatibility path:

```text
f ∘ p₁ = g ∘ p₂.
```

The internal test-cone carrier should reuse an existing Hom fibre rather than
introduce a manual commuting-square record. At a test object `T`, the primary
cone is an arrow

```text
h : T → A ⊕ B
```

together with its point in the annihilator fibre of precomposition by `d` at
zero. A conventional pair `a : T → A`, `b : T → B` with
`f ∘ a = g ∘ b` translates into that cone through biproduct pairing and the
additive cancellation laws.

The factor space is the kernel factor fibre:

```text
HFiber(
  Hom(T,P) ──(k ∘ −)──→ Hom(T,A ⊕ B),
  h).
```

Kernel universality makes this space contractible. The whole fiber-product
result must retain:

- the cospan and difference arrow;
- the selected kernel;
- `P`, `p₁`, and `p₂`;
- the compatibility path;
- the whole cone-to-factor operation;
- reconstruction and uniqueness/contractibility; and
- conventional pair-cone adapters derived from existing biproduct operations.

Likely formal owners are `ComputationalFiberProduct` and
`HasComputationalFiberProducts`; exact naming and argument order remain an
owner-audit result. This is distinct from family substitution
`Pullback_catd`, exact-slice `PullbackStructure`, and the existing weak
pullback.

## Genuine Computational Pushouts

Dually, for a span

```text
f : C → A
g : C → B,
```

form the biproduct difference map

```text
d := ⟨f,−g⟩ : C → A ⊕ B
```

using the existing biproduct injections/copairing, and select its cokernel:

```text
q : A ⊕ B → Q.
```

Define:

```text
j₁ := q ∘ ι₁ : A → Q
j₂ := q ∘ ι₂ : B → Q.
```

The cokernel law derives:

```text
j₁ ∘ f = j₂ ∘ g.
```

A primary cocone is an arrow `h : A ⊕ B → T` in the cokernel coannihilator
fibre at zero. Its factor space

```text
HFiber(
  Hom(Q,T) ──(− ∘ q)──→ Hom(A ⊕ B,T),
  h)
```

is contractible. The whole result retains the span, difference map, selected
cokernel, object, injections, compatibility, factor operation,
reconstruction, uniqueness, and conventional copair adapters.

The construction should be a direct dual at the mathematical layer, but the
active implementation may use a narrow mirror owner where a post-`Op` term
would lose the rigid head needed by consumers. Any such choice requires an
owner-position probe and must not become a duplicated parallel additive
theory.

## Stability Needed By The Snake Algorithm

The CAP construction relies on two standard Abelian facts:

```text
pullback of an epimorphism is epic;
pushout of a monomorphism is monic.
```

For a fiber product of `ι : I → X` and `ε : E → X`, with `ε` epic, the
projection `p₁ : I ×ₓ E → I` must carry explicit epicity evidence. Dually,
for a pushout of `μ : K → C` and `π : K → P`, with `μ` monic, the injection
`q₂ : P → C ⊔ₖ P` must carry explicit monicity evidence.

The generic proof should use the completed Abelian normality, kernel/cokernel,
and universal-factor owners. It must not postulate a Boolean stability flag or
silently call a native polynomial classifier. If the most direct proof needs a
derived image/coimage or cancellation lemma, add the smallest generic theorem
at its mathematical owner and preserve all witness data.

The native polynomial implementation may independently classify the selected
projection/injection as a differential check, but its successful witness must
agree with the generic construction's selected arrow.

## Witness-Rich Short Exact Triples

For composable arrows

```text
A ──i──→ B ──p──→ C,
```

package a short exact triple with:

- a retained path `p ∘ i = 0`;
- explicit `IsMonic(i)` evidence;
- explicit `IsEpic(p)` evidence; and
- exactness at `B`, represented computationally by epicity of the selected
  lift `A → Ker(p)` induced by `p ∘ i = 0`.

This reuses the completed exactness convention. It does not foundationally
identify selected image and kernel objects, and it does not erase the factor
algorithm into a proposition-only or Boolean result.

The whole package is needed as the stable input language for the successor
long-exact-sequence goal. It is not necessary to force every internal step of
the generic snake construction through a prepackaged short exact sequence:
the CAP algorithm canonically builds the relevant kernel/cokernel rows from
`δ` and `λ`.

## Generic Abelian Snake Connecting Morphism

The primary generic input is a composable triple

```text
A ──δ──→ B ──β──→ C ──λ──→ D
```

with an explicit path

```text
λ ∘ β ∘ δ = 0.
```

That one path supplies both tests needed to construct:

```text
γ : Coker(δ) → D        from λ ∘ β,
α : A → Ker(λ)          from β ∘ δ.
```

Let:

```text
ι : Ker(γ) → Coker(δ)
ε : B → Coker(δ)
μ : Ker(λ) → C
π : Ker(λ) → Coker(α).
```

Construct the genuine fiber product of `ι` and `ε` and the genuine pushout of
`μ` and `π`. The stability theorems provide:

```text
p₁ : FiberProduct(ι,ε) → Ker(γ)      epic,
q₂ : Coker(α) → Pushout(μ,π)         monic.
```

The fiber-product and pushout equations derive the test paths required for:

```text
u : Ker(γ) → Pushout(μ,π)
    selected by colifting q₁ ∘ β ∘ p₂ along the epic p₁;

∂ : Ker(γ) → Coker(α)
    selected by lifting u along the monic q₂.
```

The whole result must retain every intermediate construction and agreement:

- the triple and triple-zero path;
- `Coker(δ)`, `γ`, its colift reconstruction, `Ker(γ)`, and `ι`;
- `Ker(λ)`, `μ`, `α`, its lift reconstruction, `Coker(α)`, and `π`;
- the fiber product, `p₁`, `p₂`, compatibility, and epicity witness;
- the pushout, `q₁`, `q₂`, compatibility, and monicity witness;
- the normal-epi test, selected `u`, and reconstruction;
- the normal-mono test, selected `∂`, and reconstruction; and
- readable source/target observations.

No intermediate map may be accepted as a hand-written commuting square, an
opaque connecting-arrow postulate, or a chosen section/retraction. All
apparent squares and triangles arise from existing Hom fibres, universal
operations, composition, and additive laws.

## Native Polynomial Freyd Specialization

Implement the whole construction over
`AlgebraPolynomialFreydAbelianCategoryModel`. The native result should use the
existing polynomial Freyd:

```text
kernel;
kernel-lift;
cokernel;
cokernel-colift;
monomorphism-witness;
epimorphism-witness;
lift-along-monomorphism;
colift-along-epimorphism;
biproduct and additive morphism operations.
```

The result must retain exact `PresentationMorphismAgreement` values for every
required zero, compatibility, reconstruction, and relation-preservation
equation. Failed input agreement, endpoint mismatch, foreign ring, resource
limit, non-epic projection, or non-monic injection remains explicit typed
failure; no witness is fabricated.

At least these native consumers are required:

- one non-split polynomial-module example for which no projection section is
  available;
- a zero/identity boundary case;
- one invalid triple-zero input;
- deterministic repeated execution; and
- comparison with the constant-field case.

The non-split example is the decisive consumer. A construction that works only
because the chosen data split has not achieved this goal.

## CAP-Like Categorical Program And Compilation

Expose whole operation roles for:

```text
fiber-product;
fiber-product-projection-1;
fiber-product-projection-2;
fiber-product-lift;
pushout;
pushout-injection-1;
pushout-injection-2;
pushout-colift;
short-exact-triple;
snake-connecting-morphism.
```

Exact role names must follow the current category-operation naming audit.
Derived methods record prerequisites rather than embedding a second matrix
algorithm. The snake method trace must expose the CAP dependency chain:

```text
cokernel-colift
  → kernel
  → cokernel
  → kernel-lift
  → fiber-product
  → pushout
  → colift-along-epimorphism
  → lift-along-monomorphism.
```

One direct native execution and one compiled computation-graph execution must
serialize to the same complete selected result. The categorical program
remains backend-neutral; matrix syntax and polynomial reduction belong below
its lowering boundary.

If the current retained IR cannot bind an intermediate whole result needed by
a later node, first test whether one whole derived snake operation with
declared prerequisites is sufficient, as in the completed homology slice. Add
a generic dependent-result binding only when the concrete consumer proves it
necessary; do not special-case snake syntax in the graph engine.

This architecture subsumes the relevant CAP/homalg layering while retaining a
tighter formal connection:

```text
categorical snake algorithm
  → selected universal operations
  → compiled algebra graph
  → native polynomial Freyd algorithms
  → retained formal equations.
```

CAP and homalg remain design and differential references, not runtime
dependencies or authorities over emdash's current representations.

## Formal Witnessed Freyd Surface

The generic rule-free snake owner may quantify over a closed
`ComputationalAbelianCategory`. The polynomial formal layer has a deliberately
different effectiveness boundary: `CommRingFreydWitnessedAbelian` is
capability-indexed and does not decode arbitrary paths in set-truncated Homs.

Therefore the formal polynomial specialization must retain the explicit raw
agreements produced by the effective TypeScript consumer. Its input/result may
include:

- the finite-free weak-kernel capability;
- four presentations and raw `δ`, `β`, `λ` morphisms;
- the raw triple-zero agreement;
- the derived fiber-product and pushout raw data;
- the explicit projection-epic and injection-monic agreements; and
- the two normal-factor test agreements.

The formal owner should construct as much of this data as existing witnessed
kernel/cokernel/normality operations permit and take only the remaining
effective agreements as explicit inputs. Every readable quotient path must be
derived through the existing agreement-to-path owners. Do not add a quotient
decoder, closed ring-wide Abelian claim, opaque connecting map, or a parallel
formal matrix algorithm.

## Proof–CAS Consumer

Extend the selected proof–CAS architecture by replaying the actual native and
categorical snake operation and reifying exact equations for at least:

- the input triple composite equaling zero;
- the `γ` cokernel-colift reconstruction;
- the `α` kernel-lift reconstruction;
- fiber-product compatibility;
- both fiber-product projection reconstructions for the selected factor;
- pushout compatibility;
- both pushout injection reconstructions for the selected cofactor;
- epicity witness data for `p₁`;
- monicity witness data for `q₂`;
- the normal-epi colift reconstruction defining `u`; and
- the normal-mono lift reconstruction defining `∂`.

Adapters must compare canonical serialization of the complete selected whole
result before adopting named equations. These equations are computational
interface facts, not proof certificates, a ring-wide theorem, or new trusted
Core syntax.

## Generalized-Morphism Boundary

Audit the existing `AlgebraModuleGeneralizedSpan` and the homalg generalized-
morphism implementation as reference evidence, but do not make the current
span the primary connecting-map owner:

- it is field-specific;
- it uses monic source aids; and
- it does not directly match the existing universal-operation architecture.

CAP's direct fiber-product/pushout algorithm is the selected design for this
goal. Three-arrow, cospan, or generalized-morphism calculi remain reserved for
later Serre quotient, derived-category, and spectral-sequence consumers. This
is a sequencing decision, not a claim that generalized morphisms are
unimportant.

## No Manual Diagrams Or Split-Epi Assumptions

Every apparent square, triangle, cone, or cocone must arise from:

- an existing internal Hom fibre;
- biproduct pairing/copairing and additive cancellation;
- a kernel/cokernel universal point and its contractible factor space;
- normal monomorphism/epimorphism factor data;
- a raw presentation agreement; or
- a whole categorical operation.

Do not introduce a semantic diagram record whose main payload is a manually
entered commutativity equation. Do not postulate the connecting arrow. Do not
choose a section of an arbitrary epimorphism or a retraction of an arbitrary
monomorphism.

## Computation And Rule Policy

- Start with transparent semantic definitions and theorem-level paths.
- Generic identity, composition, zero, addition, negation, biproduct,
  kernel/cokernel, normality, and agreement-to-path owners remain unchanged.
- Add a runtime rule only for a genuinely new constructor-visible whole owner
  with a measured consumer.
- Use proof-time unification only between suitable rigid heads and normalized
  semantic bodies, validated by typed `eq_refl`.
- Follow inferred-slot SOP: compound reducible endpoints do not belong in
  nondiscriminating rule-LHS positions.
- A dual formulation through `Op_*` must preserve whole higher action and
  usable rigid heads; warning increases alone are not a veto.
- Warnings are diagnostics, not vetoes; timeout, subject-reduction failure,
  retained-action loss, false positive conversion, or unjoinable semantics are
  rejection signals.
- Never add broad global `id`, `comp_fapp0`, `fapp*`, biproduct, or quotient
  rewrites merely to expose one snake computation.
- Prefer a rule-free implementation when existing universal operations already
  compute the selected results.

## Implementation Ledger

| ID | State | Dependencies | Required result |
|---|---|---|---|
| `ASC-PLAN-0` | complete; checkpoint `8cb81eaf` | baseline `4036ef47` | living plan, isolated branch/worktree, preparatory integration evidence, scope/Git boundary, persistent goal |
| `ASC-AUDIT-1` | complete; checkpoint `771f082b` | active formal/native/category/proof–CAS owners and CAP source | exact owner and endpoint matrix, focused baselines, operation dependencies, rejection signals |
| `ASC-NATIVE-SQUARES-1A` | complete; checkpoint `771f082b` | native Freyd biproduct/kernel/cokernel owners | derived whole fiber product and pushout, selected factor/cofactor, quotient uniqueness, focused positive/negative/determinism tests |
| `ASC-FIBER-2` | complete; checkpoint `9a73e59b` | biproducts and computational kernels | genuine rule-free fiber product, internal cone, contractible factor space, projections and compatibility |
| `ASC-PUSHOUT-3` | complete; checkpoint `9a73e59b` | biproducts and computational cokernels | genuine rule-free pushout, internal cocone, contractible cofactor space, injections and compatibility |
| `ASC-STABILITY-4` | complete; checkpoint `9d637cdd` | genuine fiber products/pushouts and Abelian normality | pullback-of-epi epic and pushout-of-mono monic with explicit witnesses |
| `ASC-IMAGE-BIMORPHISM-4A` | complete; checkpoint `ec022ddb` | generic image/coimage comparison | canonical comparison is constructively monic and epic from visible Abelian capabilities, with a public one-capability wrapper and paired bimorphism value |
| `ASC-BIMORPHISM-LEMMAS-4A1` | complete; checkpoint `e98a5663`; path-combinator extension included in 4A | generic kernels/cokernels and additive cancellation | zero selected kernel implies monic, zero selected cokernel implies epic, both properties compose, and reusable factorization/fiber/pushout annihilation paths retain canonical endpoints |
| `ASC-EXACT-5` | complete; checkpoint `84ebee12` | generic homology exactness and monic/epic owners | witness-rich short exact triple and canonical readable observations |
| `ASC-SNAKE-GENERIC-6` | in progress via 6A | rows 2–5 | generic CAP-style connecting morphism with every intermediate whole result and path retained |
| `ASC-SNAKE-SPINE-6A` | complete; checkpoint `aa0d1be4` | generic kernels/cokernels and triple-zero path | internal triple plus selected `epsilon`, `gamma`, `iota`, `mu`, `alpha`, `pi`, and both first-factor reconstructions |
| `ASC-SNAKE-SQUARES-6B` | complete; checkpoint `dcaabb1d` | 6A and generic stability | selected `FiberProduct(iota,epsilon)`, `Pushout(mu,pi)`, epic `p1`, and monic `q2` |
| `ASC-SNAKE-NATIVE-7` | core algorithm green; category/serializer checkpoint pending | operational polynomial Freyd Abelian provider | non-split polynomial whole result, failures, deterministic serialization, boundary consumers |
| `ASC-CATEGORY-8` | pending | categorical operation registry/compiler | operation roles, methods, prerequisite trace, lowering, direct/graph whole-result agreement |
| `ASC-FORMAL-9` | pending | witnessed formal Freyd Abelian operations | rule-free capability-indexed connecting result with explicit raw agreements and reviewers |
| `ASC-BRIDGE-10` | pending | native/category/formal selected results | proof–CAS delegation bundle and exact equation replay |
| `ASC-DIFFERENTIAL-11` | pending | field implementation and CAP/homalg references | constant-field/CAP differential evidence without split assumptions or runtime dependency |
| `ASC-CLOSE-12` | pending | all required rows | authorities, warning/LHS/catalog/health evidence, focused gates, checkpoints, successor boundary |

Rows may be split or reordered when a focused audit refines their dependency
graph. A row may be rejected or deferred only with durable evidence and a
concrete replacement, prerequisite, or human decision.

## Initial Decision Ledger

| ID | State | Decision |
|---|---|---|
| `D-ASC-001` | accepted | The next owner is the general non-split Abelian connecting morphism, not the long exact sequence. |
| `D-ASC-002` | accepted | Genuine fiber products are kernels of `[f,−g]`; genuine pushouts are cokernels of the dual difference map. |
| `D-ASC-003` | accepted | Their primary cones/cocones and factor spaces reuse internal Hom fibres; no manual square record is introduced. |
| `D-ASC-004` | accepted | Contractibility, not mere existence, distinguishes these owners from the existing computational weak pullbacks. |
| `D-ASC-005` | accepted | The CAP fiber-product/pushout construction is primary because it does not choose a section of an epimorphism. |
| `D-ASC-006` | accepted | The field connecting implementation is differential evidence only; its `projectionSection` is not generalized to polynomial Freyd modules. |
| `D-ASC-007` | accepted | Pullback-of-epi and pushout-of-mono stability are explicit generic witness-producing theorems, not native Boolean side checks. |
| `D-ASC-008` | accepted | Short exactness retains zero, monic, epic, and boundary-to-kernel epicity data; selected image/kernel objects are not definitionally identified. |
| `D-ASC-009` | accepted | The snake owner takes a composable triple with a retained triple-zero path and stores every intermediate universal construction. |
| `D-ASC-010` | accepted | Whole categorical operations own computation; polynomial matrices and reductions stay below backend-neutral lowering. |
| `D-ASC-011` | accepted | The formal polynomial surface remains capability- and agreement-indexed; no arbitrary quotient-path decoder or closed formal Abelian instance is claimed. |
| `D-ASC-012` | accepted | Generalized morphisms are audited but deferred as the primary calculus until a Serre-quotient, derived, or spectral-sequence consumer requires them. |
| `D-ASC-013` | accepted | No runtime rule, unifier, stable head, or categorical-IR extension is assumed before an owner-position consumer demonstrates the need. |
| `D-ASC-014` | accepted | Long exact homology, chain homotopy, derived localization, spectral sequences, and Čech cohomology are successor goals. |
| `D-ASC-015` | accepted after formal owner probes | Genuine fiber products reuse the existing weak-pullback cone and compatibility adapters through a transparent genuine-kernel-to-weak-kernel view; contractible kernel factors supply the extra universal content. |
| `D-ASC-016` | accepted after formal pushout probe | The direct pushout mirror uses `iota_1 o alpha + iota_2 o (-gamma)`. Its cokernel annihilation derives ordinary compatibility; conventional copairs and both injection laws are theorem-level consequences. No `Op_*` runtime surface or rule is needed. |
| `D-ASC-017` | accepted after native CAP consumer | The complete CAP operation chain executes over polynomial Freyd using selected epic/monic witnesses for the actual fiber-product projection and pushout injection. The published rational example induces the expected `-1` quotient map. |
| `D-ASC-018` | accepted after nonsplit consumer | With `delta=x`, `beta=id`, and `lambda=0`, the algorithm computes through the nonsplit quotient `R -> R/(x)` and uses no projection section. This is the decisive rejection of the older field-only construction as general authority. |
| `D-ASC-019` | classified after source-health refresh | Registering the two new formal sources invalidated the resumable health-set identity and triggered one full rebuild. Every new owner/reviewer passed, but the unrelated existing `examples/dependent_simplex_faces.lp` failed; the same focused failure reproduces on clean baseline `main`. The generated health report correctly remained unchanged. This goal records and excludes that orthogonal baseline defect rather than editing simplex work. |
| `D-ASC-020` | accepted after exactness owner probe | `ComputationalExactAt` is `IsEpic` for the boundary-to-selected-kernel map already constructed by `ComputationalHomologyAt`. `ComputationalShortExactTriple` adds incoming monicity and outgoing epicity over the same internal zero pair; it stores no image/kernel equality or new diagram. |
| `D-ASC-021` | accepted after constructive stability proof | Stability is proved for the canonical selected binary constructions, so their combined arrows are definitionally the kernel/cokernel selected by the same `ComputationalAbelianCategory`. The difference arrow first inherits epicity/monicity from the distinguished leg; normal epi/mono factors then turn equality after the projection/injection into a zero difference. |
| `D-ASC-022` | accepted after generic spine probe | The generic snake input is one internal Sigma triple retaining `delta`, `beta`, `lambda`, and `lambda o beta o delta = 0`. That single path constructs both the `lambda beta` cokernel cone and the `beta delta` kernel cone, so `gamma` and `alpha` are selected operations rather than diagram fields. |
| `D-ASC-023` | accepted after generic square-stage probe | CAP's fiber product and pushout are the canonical constructions selected by the same `ComputationalAbelianCategory`; therefore the already-proved stability theorems apply without transport or a second choice and return the exact epic `p1` and monic `q2` needed by normality. |
| `D-ASC-024` | initial prerequisite hypothesis; refined by `D-ASC-027` | The first audit proposed factoring an `epsilon`-annihilated arrow through an epic image coastriction and therefore scheduled the canonical comparison bimorphism. The theorem remains a useful Abelian foundation and was completed, but the later dual review found a shorter proof from the pre-Abelian cone/cocone consequences alone. |
| `D-ASC-025` | accepted after cancellation-converse probe | Monicity from a zero selected kernel and epicity from a zero selected cokernel are constructive: factor the arbitrary difference through the contractible kernel/cokernel space, replace the structural arrow by zero, and cancel the additive difference. Named cone/factor observations are required to keep endpoint inference rigid. |
| `D-ASC-026` | accepted after comparison-bimorphism owner audit | The comparison proof must use one literal pre-Abelian owner presentation. Whole-file and downstream probes that compared a canonical coimage with a second transparent reconstruction exceeded 90 seconds without a type error. Passing the pre-Abelian package and its two normality capabilities explicitly keeps the `ComputationalAbelianCategory` constructor visible at stability calls; public one-capability wrappers then check in under 20 seconds. No opacity, unifier, axiom, or weaker theorem is needed. |
| `D-ASC-027` | refined after the completed dual proof | The full comparison bimorphism is a reusable Abelian foundation, but the snake normal tests need not route through an epic coastriction. The stronger pre-Abelian cone/cocone consequences now derive directly that the coimage projection kills every kernel cone and every cokernel cocone kills the image embedding. The final snake tranche should use these shorter canonical paths while retaining the independently completed comparison theorem. |

## Implemented Genuine Binary Universal Constructions

`emdash3_2_computational_fiber_products.lp` defines the genuine fiber product
as the selected kernel of the same additive difference used by weak
pullbacks. A transparent genuine-kernel-to-weak-kernel view preserves the
existing cone and ordinary compatibility interface, while the underlying
`KernelFactorSpace` supplies contractibility and uniqueness. Stable readable
observations expose the object, combined kernel arrow, both projections,
selected lift, combined and projected reconstruction, and uniqueness.

`emdash3_2_computational_pushouts.lp` is the direct rule-free mirror. Its
difference is the sum of the two injection composites, with the second leg
negated. The selected cokernel supplies the object, combined projection,
injections, contractible cofactor space, selected cofactor, reconstruction,
and uniqueness. Additive lemmas derive ordinary compatibility and translate a
conventional compatible copair into the internal coannihilator fibre.

Both files pass quiet and warning-enabled owner checks. They add no rewrite or
unification rule and have zero strict-LHS findings.

The source registry and generated check catalog include both owners and the
reviewer. A required health refresh checked the complete invalidated source
set once: the new files were green, but the report was not rewritten because
the unrelated baseline `dependent_simplex_faces` reviewer fails identically on
`main`. Later work reuses focused evidence and does not repeat that aggregate.

## Implemented Native CAP Core

The TypeScript layer now has derived whole polynomial Freyd fiber products and
pushouts with explicit quotient agreements and uniqueness operations. The
native stability adapter retains the supplied epic/monic witness, checks that
it classifies the selected cospan/span leg, and independently constructs the
actual projection/injection witness.

`algebraPolynomialFreydSnakeConnecting` follows the reviewed CAP operation
order exactly. Its frozen whole result retains both first universal factors,
the genuine fiber product and pushout, stability witnesses, the normal-epi
colift `u`, the normal-mono lift defining the connecting map, and all
reconstruction agreements. It passes the CAP rational example and the
nonsplit `R -> R/(x)` example; the latter contains no section field. Category
roles, canonical whole serialization, and formal replay remain in later rows.

## Implemented Short Exact Interface

`emdash3_2_short_exact_sequences.lp` packages the selected computational
notion required by later long-exact-sequence assembly. Exactness is epicity of
the actual boundary-to-kernel lift. Short exactness additionally retains
monicity of the incoming arrow and epicity of the outgoing arrow, while the
zero composite remains the existing `ComputationalChainPair` HFiber point.
The owner and reviewer pass quiet and warning-enabled checks, add no rule, and
have zero strict-LHS findings.

## Implemented Generic Abelian Stability

`emdash3_2_abelian_fiber_pushout_stability.lp` proves both witness-producing
stability results. For fiber products, equality after the first projection is
converted to an annihilated extension on the biproduct. The epic difference
map's normal colift is forced to zero by the original epic second leg, which
proves the first projection epic. The pushout proof is the exact direct dual:
the monic difference's normal lift is forced to zero by the original monic
first leg, proving the second injection monic.

The final values inhabit `IsEpic` and `IsMonic`, so downstream snake
computation receives the actual cancellation evidence. The owner and reviewer
pass quiet and warning-enabled checks at the inherited `1,217` critical-pair
and `169` replaceable-variable import boundary. The module adds no rule or
unifier and has zero strict-LHS findings.

## Implemented Generic Snake Spine

The first generic snake tranche is active in
`emdash3_2_abelian_snake_lemma.lp`. `AbelianSnakeTriple` retains exactly three
composable arrows and their triple-zero path. The same path constructs the
cokernel cone selecting `gamma : Coker(delta) -> D` and the kernel cone
selecting `alpha : A -> Ker(lambda)`. Their reconstruction paths, the kernel
embedding `iota`, the kernel embedding `mu`, and the cokernel projection `pi`
are all named observations of existing universal owners.

This spine passes quiet and warning-enabled checking, adds no rule or unifier,
and has zero strict-LHS findings. The fiber product, pushout, their stability
witnesses, the two derived normal-factor tests, and the final connecting arrow
remain in the parent 6 row.

The second tranche now selects `FiberProduct(iota,epsilon)` and
`Pushout(mu,pi)` and exposes all four structural arrows. The generic stability
owners construct epicity of `p1` from the selected cokernel projection
`epsilon` and monicity of `q2` from the selected kernel embedding `mu`.
Reviewer assertions check both exact cancellation types. The two normal-factor
test paths and their selected colift/lift remain the final 6C tranche.

The 6C audit first exposed the canonical image/coimage cancellation layer. The
first prerequisite tranche is implemented in
`emdash3_2_preabelian_bimorphism_lemmas.lp`. It proves both directions missing
from the earlier one-way cancellation observations: a zero selected kernel
embedding constructs `IsMonic`, and a zero selected cokernel projection
constructs `IsEpic`. Each proof forms the additive difference cone, selects
its unique universal factor, replaces the structural arrow by zero, and
cancels the difference. Generic composition preserves both properties. Named
transparent cones and factors avoid repeating reducible `HFiber` expressions
inside higher-order equality arguments. Generic factorization-annihilation and
fiber/pushout path combinators now keep the comparison proof at one canonical
endpoint presentation.

The complete comparison tranche is implemented in
`emdash3_2_abelian_image_bimorphisms.lp`. For monicity it pulls the epic
coimage projection back along the selected kernel of the comparison. The
factorization of `f`, the selected image/coimage annihilation consequences,
and epic cancellation force that kernel embedding to zero. The epic proof is
the direct pushout dual: push out the monic image embedding along the selected
comparison cokernel and use monic cancellation to force its projection zero.
The zero-kernel and zero-cokernel converses then construct the actual
`IsMonic` and `IsEpic` functions.

The initially attempted downstream and whole-owner variants mixed the
canonical `computational_coimage_object` with a second transparent expansion
of the same cokernel-of-kernel. Their proofs were mathematically valid but
exceeded the 90-second checker bound during conversion. The accepted
implementation instead retains one literal `PreAbelianCategory` parameter and
passes its normal-mono and normal-epi capabilities separately, so the
constructed Abelian package reduces immediately only at the two stability
calls. Public wrappers consume one arbitrary `ComputationalAbelianCategory`.
Quiet and warning-enabled owner and reviewer checks are green; the files add
no rule or unifier and inherit exactly the `1,217` critical-pair and `169`
replaceable-variable import boundary.

A final dependency review found that the snake normal tests can use the
shorter pre-Abelian consequences directly: every cocone of `delta` kills its
selected image embedding, and the coimage projection kills every kernel cone.
Thus the comparison bimorphism remains a completed reusable Abelian theorem,
while the snake construction does not introduce a needless coastriction
detour or accept either normal test as data.

## Baseline And Validation Policy

Use proportional, bounded checks. Do not run repository-wide TypeScript,
kernel, book, print, package, or release aggregates merely for reassurance.

### Planning and audit

- inspect exact staged and unstaged diffs and all worktrees;
- verify baseline ancestry and branch identity;
- run `workspace:check`;
- locate owners and consumers with `rg`;
- run only the relevant completed Abelian, weak-pullback, homology,
  categorical-program, proof–CAS, and field-reference suites;
- check the relevant Lambdapi owners/reviewers with each target bounded to 90
  seconds; and
- record warning/LHS/catalog/health baselines before formal changes.

### TypeScript implementation

- root typecheck and affected-file lint;
- focused positive, negative, non-split, endpoint, foreign-ring, bounded, and
  determinism tests;
- direct operation, category method, planner, compiler, graph, and reference
  execution;
- exact whole-result serialization comparisons; and
- no complete `check:ts` unless a genuinely affected shared integration
  boundary and current user scope authorize it.

### Lambdapi implementation

- smallest owner-position probe and first real consumer;
- quiet and warning-enabled checks;
- explicit import-union warning classification;
- strict inferred-slot/LHS audit;
- positive reviewer and negative/noncollapse boundary;
- source registration, catalog, and health synchronization; and
- bounded integration only at the coherent semantic boundary.

### External differential

- deterministic injected adapter or checked fixture first;
- installed external processes remain opt-in and non-authoritative;
- mismatch remains observable; and
- native/formal execution never depends on GAP/CAP, homalg, Singular, or the
  field reference implementation.

## Rejection Signals

Refine or reject a candidate when it:

- chooses a section of a general epimorphism;
- represents universality, compatibility, exactness, monicity, or epicity only
  by Booleans;
- asks users to hand-write cone/cocone squares instead of deriving/adopting
  internal Hom-fibre data;
- returns a weak nonunique factor where the snake construction needs a
  contractible factor space;
- assumes quotient-path decoding or selected-object equality;
- postulates the connecting morphism without its universal-operation trace;
- duplicates identity, composition, biproduct, kernel/cokernel, normality, or
  Freyd quotient owners;
- treats the field-linear or CAP runtime representation as polynomial Freyd
  authority;
- caps a whole construction required by a later universal operation;
- introduces a snake-specific categorical AST instead of the retained IR;
- adds broad hot-head runtime rewrites; or
- depends on an unrelated or orthogonal worktree.

## Completion Boundary

The goal is complete only when:

- genuine generic fiber products and pushouts are internally derived from
  selected biproducts and kernels/cokernels;
- their factor/cofactor spaces are contractible and conventional
  compatibility adapters are available;
- pullback-of-epi and pushout-of-mono stability produce explicit witnesses;
- short exact triples have a witness-rich reusable interface;
- the generic CAP-style snake connecting morphism retains every intermediate
  construction and path;
- a genuinely non-split polynomial Freyd example computes;
- one categorical snake program lowers and agrees with direct execution;
- the witnessed formal boundary checks without a quotient decoder;
- proof–CAS replays the selected construction and exact equations;
- field/CAP/homalg differential evidence remains non-authoritative;
- every rule or unifier, if any, has complete owner-position SOP evidence;
- focused tests, typecheck, lint, formal reviewers, warnings, audits, catalog,
  health, and standing authorities are synchronized; and
- every ledger row is implemented, rejected with durable evidence, or
  explicitly deferred behind a concrete prerequisite.

The goal does not complete merely because the existing split field example or
a direct matrix formula returns an arrow.

## Deliberate Non-Goals

- the full long exact homology sequence or its term-by-term exactness proof;
- arbitrary quotient-path decoding or choice;
- a closed formal polynomial Freyd `AbelianCategory` claim;
- chosen splittings for arbitrary epis or monos;
- replacement of exact-slice pullbacks or generic family substitution;
- three-arrow/generalized-morphism calculus as the primary implementation;
- chain homotopies, quasi-isomorphisms, or derived-category localization;
- unbounded complexes, bicomplexes, DG categories, spectral sequences, or
  spectral algebraic geometry;
- varying-ring/semilinear Čech complexes or Čech cohomology;
- GAP/CAP API compatibility, CompilerForCAP AST recovery, or an external CAS
  runtime dependency;
- parser, hosted service, package publication, push, merge, or release; and
- integration of path-cubical/global-strictness work.

## Sources And Design References

- completed Freyd homology plan:
  `docs/TYPESCRIPT_EMDASH_FREYD_HOMOLOGY_COMPUTATION_PLAN.md`;
- completed Freyd Abelian plan:
  `docs/TYPESCRIPT_EMDASH_FREYD_ABELIAN_COMPUTATION_PLAN.md`;
- focused CAS/CAP-aware architecture:
  `docs/TYPESCRIPT_EMDASH_FOCUSED_CAS_AND_CATEGORICAL_ENGINE_PLAN.md`;
- proof–CAS delegation architecture:
  `docs/TYPESCRIPT_EMDASH_PROOF_CAS_DELEGATION_PLAN.md`;
- active generic kernel/cokernel, Abelian, weak-pullback, and homology owners
  under `emdash2/`;
- active polynomial Freyd and field-reference sources under `src/v3_2/`; and
- CAP `SnakeLemmaImplementation.tex` and related CAP/homalg sources at the
  reviewed local-source commit recorded above.

These sources guide decomposition and differential checks. Active code,
focused diagnostics, and repository SOP remain implementation authority.

## Persistent `/goal` Launch Prompt

Implement `TS-EMDASH-ABELIAN-SNAKE-CONNECTING` in
`/home/user1/emdash1-abelian-snake-v1` on
`goal/abelian-snake-connecting-v3.2`, delegating every evolving owner audit,
generic genuine fiber-product/pushout formulation, stability proof,
short-exact interface, generic snake construction, native polynomial Freyd
whole result, categorical operation and lowering result, formal witnessed
construction, proof–CAS consumer, external differential, warning
classification, validation result, checkpoint, and completion condition to
this living plan. Preserve baseline
`4036ef47be6c3f82dcac05c257c98b2201c101d7` as comparison evidence. Preserve
whole universal-construction owners, contractible factor spaces, explicit raw
agreements, generic identity/composition/biproduct/kernel/cokernel ownership,
backend-neutral categorical lowering, the existing Freyd quotient
architecture, and the non-split Abelian boundary. Follow root/nested
persistent-goal and Lambdapi SOP; keep every Lambdapi target bounded to 90
seconds; avoid unrelated aggregates; make only local validated checkpoint
commits after synchronizing the exact staged diff and ledger. Do not push,
merge, publish, release, create a PR, amend, rebase, reset, rewrite history,
delete branches, or remove worktrees. Do not claim arbitrary quotient
effectiveness or begin the long exact sequence, derived categories, spectral
sequences, or orthogonal cubical/strictness integration. The goal completes
only when every scoped row is implemented, rejected with durable evidence, or
explicitly deferred behind a concrete prerequisite and all affected
authorities are synchronized.
