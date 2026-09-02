# Abelian Snake Connecting Owner Audit

Date: 2026-09-02

Status: active audit evidence for
`TS-EMDASH-ABELIAN-SNAKE-CONNECTING`

Baseline: `4036ef47be6c3f82dcac05c257c98b2201c101d7`

## Audit Question

What is the smallest computational-and-internal owner graph that constructs a
general Abelian snake connecting morphism without choosing a splitting, adding
a manual diagram grammar, or duplicating the existing Freyd quotient?

The reviewed answer is:

```text
genuine fiber product = kernel of a biproduct difference
genuine pushout       = cokernel of the dual difference

CAP snake algorithm
  = cokernel-colift + kernel-lift
  + fiber product + pushout
  + pullback/pushout stability
  + normal-epi colift + normal-mono lift.
```

The current field connecting implementation is not the general answer because
it begins with a chosen `projectionSection`. Polynomial-module epimorphisms do
not generally split.

## Existing Formal Owners

| Need | Active owner | Exact usable boundary |
|---|---|---|
| Set-valued additive Homs | `emdash3_2_preadditive_categories.lp` | zero, addition, negation, and bilinear generic composition |
| Selected biproduct | `emdash3_2_additive_categories.lp` | product object, projections, injections, pairing, copairing, beta/eta paths |
| Difference cone | `emdash3_2_computational_weak_pullbacks.lp` | `[f,−g]`, annihilator-HFiber cone, selected nonunique weak factor |
| Conventional equality adapter | `emdash3_2_computational_weak_pullback_compatibility.lp` and `_cones.lp` | difference-zero ⇄ equalizing pair without a square record |
| Genuine kernel | `emdash3_2_kernels_cokernels.lp` | object, embedding, annihilation, contractible factor fibre, lift, reconstruction, uniqueness |
| Genuine cokernel | `emdash3_2_kernels_cokernels.lp` | object, projection, annihilation, contractible cofactor fibre, colift, reconstruction, uniqueness |
| Monic/epic cancellation | `emdash3_2_abelian_categories.lp` | `IsMonic`, `IsEpic`; kernel embeddings monic and cokernel projections epic |
| Normal factors | `emdash3_2_abelian_categories.lp` | contractible `NormalMonoLiftSpace` and `NormalEpiColiftSpace` plus selected factors and laws |
| Whole Abelian capability | `ComputationalAbelianCategory` | one selected pre-Abelian package plus normal-mono and normal-epi operations |
| Exactness convention | `emdash3_2_computational_homology.lp` and formal Freyd homology | selected boundary-to-kernel lift is epic; no selected-object equality |

The first new formal owners should therefore be rule-free transparent
compositions of these declarations. No missing kernel rule is implicated.

### Formal name separation

The new binary universal constructions must not reuse these unrelated names:

- `Pullback_catd`, which is substitution of a Cat-valued family;
- `PullbackStructure`, which selects exact-slice base change and
  `Σ_f ⊣ f*`; or
- `ComputationalWeakPullback`, whose factors are intentionally nonunique.

The candidate names are:

```text
ComputationalFiberProduct
HasComputationalFiberProducts
ComputationalPushout
HasComputationalPushouts.
```

## Existing Native Polynomial Owners

| Need | Active TypeScript owner | Retained evidence |
|---|---|---|
| Presentation biproduct | `algebraPolynomialFreydBiproduct` | object plus both injections and projections |
| Additive arrows | `algebraPolynomialPresentationMorphismAdd`, `...Negate`, `...Compose` | checked relation-preserving representatives |
| Quotient comparison | `algebraPolynomialPresentationMorphismCongruence` | explicit target-factorization agreement, including failures |
| Kernel | `algebraPolynomialFreydKernel` | two weak pullbacks, embedding, annihilation agreement |
| Kernel factor | `algebraPolynomialFreydKernelLift` / `...Unique` | selected factor, reconstruction, quotient uniqueness |
| Cokernel | `algebraPolynomialFreydCokernel` | enlarged presentation, projection, annihilation agreement |
| Cokernel cofactor | `algebraPolynomialFreydCokernelColift` / `...Unique` | selected cofactor, reconstruction, quotient uniqueness |
| Monic/epic witness | `algebraPolynomialFreydMonomorphismWitness` / `...EpimorphismWitness` | actual kernel/cokernel zero agreement |
| Normal factors | `algebraPolynomialFreydLiftAlongMonomorphism` / `...ColiftAlongEpimorphism` | selected construction with relation and reconstruction agreements |
| Operation registry | `algebraPolynomialFreydAbelianCategoryModel` | methods, prerequisites, native operations, lowerings, doctrine qualification |

The native fiber product and pushout need no new matrix primitive. They are
derived whole algorithms over this table.

## Existing Formal Polynomial Boundary

The Lambdapi Freyd package is witness-enriched rather than closed:

- raw presentation morphisms retain relation-preservation witnesses;
- quotient equality is produced from explicit presentation agreements;
- kernels/cokernels and normal factors consume the required explicit
  agreements; and
- `CommRingFreydWitnessedAbelian` does not decode arbitrary set-truncated
  quotient paths.

The snake specialization must follow the same boundary. The effective CAS may
compute and supply a finite list of raw agreements, but the formal owner must
not invent a quotient decoder or postulate the final arrow.

## CAP Endpoint Audit

CAP's tutorial implementation takes three composable arrows:

```text
A ──δ──→ B ──β──→ C ──λ──→ D
```

and implicitly requires `λ ∘ β ∘ δ = 0`. Under emdash's `after, before`
composition convention, the intended endpoints are:

| Name | Type | Construction |
|---|---|---|
| `ε` | `B → Coker(δ)` | cokernel projection of `δ` |
| `γ` | `Coker(δ) → D` | cokernel colift of `λ ∘ β` |
| `ι` | `Ker(γ) → Coker(δ)` | kernel embedding of `γ` |
| `μ` | `Ker(λ) → C` | kernel embedding of `λ` |
| `α` | `A → Ker(λ)` | kernel lift of `β ∘ δ` |
| `π` | `Ker(λ) → Coker(α)` | cokernel projection of `α` |
| `p₁` | `FiberProduct(ι,ε) → Ker(γ)` | first fiber-product projection; epic because `ε` is epic |
| `p₂` | `FiberProduct(ι,ε) → B` | second fiber-product projection |
| `q₁` | `C → Pushout(μ,π)` | first pushout injection |
| `q₂` | `Coker(α) → Pushout(μ,π)` | second pushout injection; monic because `μ` is monic |
| `u` | `Ker(γ) → Pushout(μ,π)` | colift of `q₁ ∘ β ∘ p₂` along `p₁` |
| `∂` | `Ker(γ) → Coker(α)` | lift of `u` along `q₂` |

The whole result must retain each row and the path that licenses the next one.

## Generic Fiber-Product Shape

For `f : A → C` and `g : B → C`:

```text
d := [f,−g] : A ⊕ B → C
k : P → A ⊕ B := kernel embedding of d
p₁ := π₁ ∘ k
p₂ := π₂ ∘ k.
```

The primary cone is the existing annihilator fibre of `d` at zero. The
factor space is exactly the existing `KernelFactorSpace`, so its
contractibility is inherited rather than reproved. The conventional pair
adapter uses existing pairing and additive cancellation.

The native implementation has now confirmed this owner shape. Its whole
result retains the biproduct, difference, genuine kernel, projections,
compatibility agreement, selected factors, both reconstruction agreements,
and kernel-based uniqueness.

## Generic Pushout Shape

For `f : C → A` and `g : C → B`:

```text
d := ⟨f,−g⟩ : C → A ⊕ B
q : A ⊕ B → Q := cokernel projection of d
j₁ := q ∘ ι₁
j₂ := q ∘ ι₂.
```

The primary cocone is the existing coannihilator fibre of `d` at zero. The
cofactor space is `CokernelFactorSpace`; conventional copairs use the existing
copair and additive cancellation.

The native implementation has likewise confirmed this owner shape and retains
the selected cokernel plus quotient uniqueness.

## Stability Proof Boundary

The new generic stability theorems must return actual cancellation functions:

```text
IsEpic(p₁)
IsMonic(q₂).
```

The input epic/monic evidence is not a Boolean tag. The likely constructive
proof uses the relevant universal property plus completed Abelian normality.
If an image/coimage lemma is required, it belongs in a small generic theorem
module; it must not be hidden in the native polynomial implementation.

For the first native consumer, independently computing the Freyd epic/monic
witness is acceptable as a checked specialization, but it does not replace the
generic theorem.

## Categorical And Proof–CAS Audit

The current categorical program can retain a whole derived operation with a
declared prerequisite trace; completed homology demonstrates this pattern.
No snake-specific graph node is initially needed. If dependent intermediate
binding becomes a real consumer requirement, it must be a generic IR feature.

The current formal bridge already:

- replays native operations;
- canonicalizes complete selected whole results;
- adopts exact named equations; and
- optionally checks a generated Lambdapi consumer.

The snake bridge should extend that pattern. It need not create a proof
certificate or a new trusted Core term.

## Baseline Evidence

The isolated worktree began clean at the named baseline. Initial checks are:

- `./scripts/pnpmw run workspace:check`: pass;
- focused Abelian/weak-pullback/homology/formal/field matrix: 50 tests, 48
  active passes, two expected opt-in live-probe skips, zero failures;
- direct focused Lambdapi checks of weak pullbacks, kernels/cokernels, Abelian
  categories, generic homology, and formal Freyd homology: pass within 90
  seconds per target; and
- inherited warning boundary: `1,392 = 1,223 critical pairs + 169 replaceable
  variables`, with zero strict-LHS findings at the top Freyd boundary.

The direct Lambdapi invocation printed the known inherited warning stream; it
introduced no delta. Subsequent comparisons should use the repository's quiet
and warning-summary wrappers to avoid retaining that noise.

## Rejected Immediate Designs

- Porting `projectionSection` from field homology: mathematically invalid for
  nonsplit polynomial-module epimorphisms.
- Reusing `ComputationalWeakPullback`: lacks contractible factors.
- Treating exact-slice `PullbackStructure` as a constructed binary pullback:
  wrong owner and prerequisite direction.
- Postulating fiber-product compatibility or a pushout square as record data:
  duplicates equations derived from the difference-map annihilator.
- Making generalized spans the first public owner: current implementation is
  field-specific and does not match the selected universal-operation chain.
- Adding global identity/composition/additivity rewrites: unnecessary and
  violates current runtime ownership.

## Next Dependency-Ready Slice

Promote the generic rule-free fiber-product and pushout owners and their
focused Lambdapi reviewers, while completing the already green native
fiber-product/pushout tests. Then prove the two stability theorems before
starting the connecting morphism.
