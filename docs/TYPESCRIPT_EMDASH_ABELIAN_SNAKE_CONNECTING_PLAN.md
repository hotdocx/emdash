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
| `ASC-AUDIT-1` | complete; checkpoint pending | active formal/native/category/proof–CAS owners and CAP source | exact owner and endpoint matrix, focused baselines, operation dependencies, rejection signals |
| `ASC-NATIVE-SQUARES-1A` | implementation green; checkpoint pending | native Freyd biproduct/kernel/cokernel owners | derived whole fiber product and pushout, selected factor/cofactor, quotient uniqueness, focused positive/negative/determinism tests |
| `ASC-FIBER-2` | pending | biproducts and computational kernels | genuine rule-free fiber product, internal cone, contractible factor space, projections and compatibility |
| `ASC-PUSHOUT-3` | pending | biproducts and computational cokernels | genuine rule-free pushout, internal cocone, contractible cofactor space, injections and compatibility |
| `ASC-STABILITY-4` | pending | genuine fiber products/pushouts and Abelian normality | pullback-of-epi epic and pushout-of-mono monic with explicit witnesses |
| `ASC-EXACT-5` | pending | generic homology exactness and monic/epic owners | witness-rich short exact triple and canonical readable observations |
| `ASC-SNAKE-GENERIC-6` | pending | rows 2–5 | generic CAP-style connecting morphism with every intermediate whole result and path retained |
| `ASC-SNAKE-NATIVE-7` | pending | operational polynomial Freyd Abelian provider | non-split polynomial whole result, failures, deterministic serialization, boundary consumers |
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
