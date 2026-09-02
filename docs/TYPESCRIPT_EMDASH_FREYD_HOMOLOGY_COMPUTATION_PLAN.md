# TypeScript/emdash Freyd Homology And Exactness Computation Plan

Date: 2026-09-02

Plan-ID: `TS-EMDASH-FREYD-HOMOLOGY-COMPUTATION`

Status: active on a dedicated branch/worktree

Baseline: `4acef747d4b80e92c5c653e0b6635e6817a9c909`

Branch: `goal/freyd-homology-computation-v3.2`

Worktree: `/home/user1/emdash1-freyd-homology-v1`

Decision-Response-Evidence:

- `/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-23_01a02f686142/responses/0099_2026-09-02T11-46-02Z_01a061ed-9a8a-7d90-ad6c-8b97eace45e9.md`

## Purpose

This plan governs the first computational-and-internal homology and exactness
layer shared by the generic categorical kernel, the polynomial Freyd CAS, the
CAP-like categorical-program compiler, Lambdapi, and the proof–CAS bridge.

The completed baseline supplies:

- bounded polynomial free complexes and chain maps at the direct matrix layer;
- quotient-aware homology, functorial homology, and connecting morphisms for
  the older field-linear presented-module reference implementation;
- genuine selected kernels and cokernels;
- constructive normal-monomorphism and normal-epimorphism operations;
- image/coimage comparison and computed comparison inverses;
- an operational polynomial Freyd Abelian category;
- capability-indexed witnessed formal Freyd Abelian structure; and
- a proof–CAS consumer replaying thirteen exact normality and comparison
  equations.

The next missing vertical slice is therefore:

```text
bounded polynomial complexes
  → complexes in the Freyd category
  → kernel cycles
  → boundary lift into cycles
  → cokernel homology
  → exactness and induced homology maps
  → formal equations and proof–CAS delegation.
```

This is also the next CAP/homalg architectural milestone. Homology should be
expressed once as an algorithmic categorical program over whole
kernel/lift/cokernel operations, specialized and compiled to the focused CAS,
and consumed by the formal layer. Direct matrix algorithms remain execution
engines and differential references, not the public categorical owner.

## Preparatory Integration And Git Boundary

The completed Freyd–Abelian plan had one stale active-status header. It was
corrected at checkpoint `4acef747`. Clean historical `main` was then
fast-forwarded from `7c537a6b` to `4acef747`; the reviewed ancestry was exactly
`0 23`. No path-cubical, global-strictness, or other orthogonal branch was
integrated.

The user explicitly authorized this plan, dedicated branch/worktree,
persistent goal, implementation continuation, and local validated checkpoint
commits following the repository Git SOP. This does not authorize push,
publication, release, PR creation, merge beyond the completed preparatory
fast-forward, rebase, amend, reset, history rewriting, branch deletion, or
worktree removal.

The baseline commit remains comparison and backtracking evidence. It is not
permission to discard descendant work.

## Reviewed Architectural Gap

### Existing bounded-free complexes stop below quotient semantics

`CommRingBoundedFreeComplex`, `CommRingBoundedFreeChainMap`, and their native
polynomial counterparts internalize varying ranks, differentials, adjacent
zero laws, components, and chain-map squares. They deliberately contain free
modules and matrices, not Freyd presentation objects, quotient-Hom chain laws,
exactness, or homology.

### Existing homology is a field-linear reference implementation

`algebra_homological.ts` already computes:

- bounded complexes of presented field modules;
- cycle kernels and boundary lifts;
- cokernel homology objects;
- induced homology maps;
- short exact sequences and connecting morphisms; and
- representative resolutions.

Its formula `Hₙ = Coker(Cₙ₊₁ → Ker(dₙ))` is valuable differential evidence.
Its field-specific module representation is not the primary owner for general
polynomial Freyd homology and must not be copied into the formal kernel as a
parallel theory.

### The Freyd Abelian layer now supplies the missing universal operations

The new polynomial Freyd category has the exact whole operations needed to
construct homology over the supported polynomial rings. The formal layer has
the same algorithms at a witness-rich boundary: raw chain agreements feed
kernel lifts and cokernel constructions without decoding arbitrary paths in
set-truncated Homs.

Consequently a closed formal `AbelianCategory` value remains unnecessary for
this goal. The formal construction quantifies over explicit chain,
reconstruction, and comparison agreements, just as the completed normality
layer does.

## Primary Mathematical Owner: Homology At One Degree

For one composable pair in a selected pre-Abelian category,

```text
Cₙ₊₁ ──dₙ₊₁──→ Cₙ ──dₙ──→ Cₙ₋₁
                  dₙ ∘ dₙ₊₁ = 0,
```

define cycles, the boundary-to-cycle map, and homology by:

```text
Zₙ := Ker(dₙ),
bₙ : Cₙ₊₁ → Zₙ       selected by kernel universality from dₙdₙ₊₁ = 0,
Hₙ := Coker(bₙ).
```

The whole computational result retains:

- the input objects and differentials;
- the chain-zero witness;
- the selected cycle kernel and embedding;
- the boundary lift and reconstruction law;
- the selected homology cokernel and projection; and
- all owner identities needed for downstream functoriality and proof–CAS
  replay.

The first generic owner should be a rule-free semantic construction such as:

```text
ComputationalChainPair(C,S,dNext,d,zero);
ComputationalHomologyAt(C,S,K,Q,pair);
```

Exact names and record layout remain an owner-audit decision. The construction
must project existing `ComputationalKernel`/`ComputationalCokernel` results
rather than duplicate their data.

## Exactness Is Epicity Of The Boundary Lift

At degree `n`, exactness is computationally characterized by:

```text
IsExactAt(dₙ₊₁,dₙ) := IsEpic(bₙ).
```

Equivalently, the selected cokernel projection of `bₙ` is zero. Since that
cokernel is `Hₙ`, this is the useful computational content of vanishing
homology.

This is preferred to making an identity-type equality

```text
Im(dₙ₊₁) = Ker(dₙ)
```

foundational. Equality of selected objects would introduce unnecessary
univalence/recentring pressure and obscure the actual factor algorithm. Image
and kernel comparisons may be derived later as readable consequences.

The exactness surface must retain its epimorphism/cokernel-zero witness; it
must not collapse to a Boolean-only flag.

## Whole Freyd Complexes And Chain Maps

Introduce a polynomial Freyd bounded-complex owner whose terms are
`AlgebraPolynomialPresentation` objects and whose differentials are
`AlgebraPolynomialPresentationMorphism`s. Each adjacent chain condition
retains a `PresentationMorphismAgreement` between the composite and zero.

The corresponding formal owner should recursively package presentations,
raw morphisms, and chain agreements. It may reuse the shape of the existing
bounded-free recursive spine, but it must not pretend that a quotient-Hom path
can be decoded back into an agreement.

Provide an adapter from the existing bounded-free polynomial complex by:

- viewing each free module as the relation-free presentation;
- viewing each matrix differential as the corresponding presentation
  morphism; and
- constructing the zero agreements through the existing exact matrix laws.

The first whole consumers include:

- a nontrivial Schreyer-derived complex;
- a complex of nontrivial presentations;
- an explicitly invalid adjacent composite retained as a negative result; and
- homology at an interior and endpoint degree.

Chain maps retain one component at every degree and explicit presentation
agreements for their squares. End-user usability derives these agreements by
computation; it does not ask users to hand-write commuting-square fields.

## Functorial Homology

For a chain map `f : C → D`, the induced map at degree `n` is constructed in
two universal steps:

1. the lower chain square makes `fₙ` send `Ker(dₙᶜ)` into `Ker(dₙᴰ)`, so
   kernel universality constructs the cycles map;
2. the upper chain square makes the cycles map send boundaries to boundaries,
   so cokernel universality constructs `Hₙ(f)`.

The whole result retains both factor maps and both reconstruction agreements.
At least identity and one nontrivial scalar/polynomial chain map must compute;
composition compatibility should be proved or explicitly deferred only after
an owner-position feasibility audit.

This goal requires one genuine induced homology-map consumer. It does not
require connecting morphisms or a long exact sequence.

## CAP-Like Categorical Program And Compilation

Homology should be represented at the algorithmic categorical layer as a
retained program whose primitive calls are existing roles:

```text
kernel;
kernel-lift;
cokernel;
```

Functorial homology additionally uses the corresponding factor operations for
the cycle and boundary maps. The program planner must expose its method trace,
and lowering must execute against the operational polynomial Freyd Abelian
provider.

One direct native computation and one compiled computation-graph execution
must serialize to the same whole result. If the current categorical IR cannot
bind the dependent object returned by a preceding whole construction, add the
smallest generic dependent-result binding needed by this concrete consumer;
do not special-case matrix syntax or decompile arbitrary TypeScript.

This design subsumes the successful CAP/homalg layering:

```text
categorical homology algorithm
  → selected Freyd universal operations
  → compiled algebra graph
  → native polynomial/module algorithms.
```

Unlike a separated CAP-over-homalg stack, the same selected result also feeds
the formal witness and proof–CAS layers.

## Formal Witnessed Freyd Homology

Add a rule-free formal extension after the witnessed Freyd Abelian owners. Its
primary input is:

- `W`, the finite-free weak-kernel capability;
- three presentations and two raw presentation morphisms; and
- an explicit agreement `dₙ ∘ dₙ₊₁ ~ 0`.

It constructs:

- the formal Freyd kernel presentation of `dₙ`;
- the raw boundary lift of `dₙ₊₁` and its reconstruction agreement;
- the formal Freyd cokernel presentation of that lift;
- the homology projection; and
- readable quotient paths derived from the retained agreements.

A witnessed exactness package additionally takes or computes the explicit
cokernel-projection-zero agreement for the boundary lift. It must not claim a
closed ring-wide exactness decision or fabricate an arbitrary quotient-path
decoder.

The later formal bounded-complex adapter should obtain each one-degree input
from the recursive complex spine. A one-degree owner is the mathematical
foundation; the bounded package is its iterator/consumer, not a parallel
homology theory.

## Proof–CAS Consumer

Extend the selected proof–CAS architecture with exact equations for:

- the adjacent chain composite agreeing with zero;
- boundary-lift relation preservation;
- boundary-lift reconstruction through the cycle embedding;
- the homology cokernel projection and annihilation;
- exactness via the boundary lift's cokernel-projection-zero witness;
- the induced cycles map and its kernel reconstruction; and
- the induced homology map and its cokernel reconstruction.

Every adapter must replay the actual operational/categorical homology
operation and compare the canonical serialization of the complete selected
whole result. Named equations remain explicitly adopted claims; they do not
create a ring-wide theorem, a proof certificate requirement, or a new Core
constructor.

## No Manual Diagram Or Parallel Quotient Grammar

Every apparent triangle or square must arise from existing internal data:

- a categorical composition path;
- a raw presentation agreement;
- a selected kernel/cokernel `HFiber` point and path;
- a chain-map component action; or
- a whole categorical program operation.

Do not introduce a semantic cone record with a manually supplied commuting
square, a second quotient Hom, or a Boolean-only exactness interface.

## Computation And Rule Policy

- Start with transparent semantic definitions and theorem-level paths.
- Generic identity, composition, zero, addition, kernel, cokernel, normality,
  and agreement-to-path owners remain unchanged.
- Add a runtime rule only for a genuinely new constructor-visible whole owner
  with a measured consumer.
- Use proof-time unification only between suitable rigid heads and normalized
  semantic bodies, validated by typed `eq_refl`.
- Follow inferred-slot SOP: compound reducible endpoints do not belong in
  nondiscriminating rule-LHS positions.
- Warnings are diagnostics, not vetoes; timeout, subject-reduction failure,
  action loss, or unjoinable semantics are rejection signals.
- Never add a broad global `id`, `comp_fapp0`, `fapp*`, or quotient collapse to
  expose one homology computation.

## Implementation Ledger

| ID | State | Dependencies | Required result |
|---|---|---|---|
| `FH-PLAN-0` | complete; checkpoint `26b7c2fd` | baseline `4acef747` | living plan, isolated branch/worktree, integration evidence, scope/Git boundary, persistent goal |
| `FH-AUDIT-1` | complete; checkpoint `2602afd6` | current formal/native owners | exact owner matrix, generic formulation, categorical-IR feasibility, baseline diagnostics, rejection signals |
| `FH-GENERIC-2` | complete; checkpoint `dfdc3538` | generic kernels/cokernels | rule-free one-degree chain-pair, cycles, boundary lift, homology cokernel, readable projections |
| `FH-NATIVE-3` | complete; checkpoint `5e9aaa4c` | polynomial Freyd Abelian provider | whole chain-pair and homology result with retained agreements and positive/negative cases |
| `FH-EXACT-4` | complete; checkpoint `5e9aaa4c` | normal epimorphism computation | witness-rich exactness at a degree and zero-homology comparison |
| `FH-CATEGORICAL-5` | complete; checkpoint pending | categorical IR/compiler | retained homology program, method trace, lowering, direct/graph byte agreement |
| `FH-BOUNDED-6` | ready | bounded free/Freyd spines | whole bounded Freyd complexes, free-complex adapter, degree observations, homology consumer |
| `FH-FORMAL-7` | blocked on generic/native orientation | witnessed Freyd Abelian package | formal one-degree homology, exactness witness boundary, focused reviewers |
| `FH-FUNCTORIAL-8` | blocked on homology owners | chain-map squares and universal operations | induced cycles/homology map with reconstruction; identity and one nontrivial consumer |
| `FH-BRIDGE-9` | blocked on native/formal results | proof–CAS delegation | exact selected chain, factor, homology, exactness, and induced-map equations |
| `FH-DIFFERENTIAL-10` | blocked on native homology | field reference/Singular adapters | non-authoritative comparison without replacing native Freyd data |
| `FH-CLOSE-11` | blocked on required rows | all required rows | authorities, warning/LHS/catalog/health evidence, focused gates, checkpoints, successor boundary |

Rows may be split or reordered when a focused probe refines dependencies. A
row may be rejected or deferred only with durable evidence and a concrete
replacement, prerequisite, or human decision.

## Initial Decision Ledger

| ID | State | Decision |
|---|---|---|
| `D-FH-001` | accepted | The next mathematical owner is one-degree homology in the polynomial Freyd Abelian category, not another isolated CAS primitive. |
| `D-FH-002` | accepted | `Hₙ` is constructed as the selected cokernel of the selected boundary lift into `Ker(dₙ)`. |
| `D-FH-003` | accepted | Exactness at degree `n` is represented computationally by epicity of the boundary-to-cycle map, with an explicit witness. |
| `D-FH-004` | accepted | Object equality `Im(dₙ₊₁)=Ker(dₙ)` is a derived readable comparison, not the foundational exactness carrier. |
| `D-FH-005` | accepted | The existing field-linear homology implementation is reference/differential evidence, not the general polynomial Freyd owner. |
| `D-FH-006` | accepted | Whole Freyd complexes retain raw adjacent-zero agreements; arbitrary quotient paths are not decoded. |
| `D-FH-007` | accepted | Homology is expressed as a retained categorical program over universal operations and lowered to the focused CAS. |
| `D-FH-008` | accepted | One induced homology map is required; connecting morphisms and long exact sequences are later goals. |
| `D-FH-009` | accepted | Proof–CAS replays actual whole operations and reifies exact equations without requiring proof certificates. |
| `D-FH-010` | accepted | No runtime rule, unifier, stable head, or categorical-IR extension is assumed before an owning-position consumer demonstrates the need. |
| `D-FH-011` | accepted | Derived categories, quasi-isomorphism localization, chain homotopy, spectral sequences, and Čech cohomology are out of scope. |
| `D-FH-012` | accepted after categorical-IR audit | Current retained programs cannot assemble dependent kernel/lift/cokernel inputs across unary nodes and do not inline derived callbacks. The first categorical consumer retains one whole `homology-at` operation with declared universal-operation prerequisites and a native lowering; generic dependent record assembly remains consumer-gated. |
| `D-FH-013` | accepted after owner audit | Generic homology construction requires only selected pre-Abelian kernels/cokernels. Abelian normality enters exactness and comparison theorems, not the existence of `Hₙ`. |
| `D-FH-014` | accepted after native agreement audit | The chain-pair constructor retains negative agreements; the homology constructor consumes only a positive chain agreement and returns a typed failure otherwise. |
| `D-FH-015` | accepted after generic owner implementation | `ComputationalHomologyAt` is a whole snapshot over one selected `PreAbelianCategory`: it retains the selected cycle kernel and the selected cokernel of the kernel-lifted boundary. Its readable equations are exactly the existing kernel reconstruction and cokernel annihilation paths. |
| `D-FH-016` | accepted after native homology tests | Native chain-pair construction always retains the computed presentation agreement, including `agrees=false`; `algebraPolynomialFreydHomologyAt` consumes only a positive pair and composes the existing Freyd kernel, kernel-lift, and cokernel owners into one frozen whole result. |
| `D-FH-017` | accepted after exactness tests | `algebraPolynomialFreydExactnessAt` compares the selected homology projection with zero. A positive comparison is retained together with the actual `AlgebraPolynomialFreydEpimorphismWitness` for the boundary map; a negative result retains the failed agreement and has no fabricated witness. |
| `D-FH-018` | accepted after categorical compilation tests | The first retained program is genuinely compositional at the available whole-operation boundary: a chain-pair input feeds derived `homology-at`, whose output feeds derived `exactness-at`. Planner prerequisites record kernel/kernel-lift/cokernel and epimorphism capabilities; direct and two-node graph execution have identical canonical outputs. No dependent-record IR extension is needed. |

## Implemented Owner Audit

The exact owner matrix, mathematical typing, formal/raw boundary, categorical-
IR limitation, baseline diagnostics, and revised sequencing are recorded in
`docs/TYPESCRIPT_EMDASH_FREYD_HOMOLOGY_OWNER_AUDIT.md`. The audit selects a
rule-free generic one-degree owner as the first semantic tranche. It rejects
both a second quotient grammar and a homology-specific categorical AST.

## Implemented Generic One-Degree Homology

`emdash3_2_computational_homology.lp` implements the selected rule-free
generic owner. `ComputationalChainPair` packages two arrows and the ordinary
zero-composite path, and exposes the same data as a `WeakKernelAnnihilator`.
`ComputationalHomologyAt` retains the selected kernel of the lower
differential and the selected cokernel of the lifted upper differential.

Readable projections expose cycles, cycle object/embedding, boundary,
boundary reconstruction, homology cokernel/object/projection, and projection
annihilation. The owner and focused reviewer pass quiet checking. No runtime
head, rewrite, unifier, image equality, exactness assertion, or manual diagram
was added. Warning-enabled checking is neutral at
`1,386 = 1,217 critical pairs + 169 replaceable variables`; strict LHS remains
clean, and the refreshed source-metrics health snapshot covers 427 files.

## Implemented Native Homology And Exactness

`src/v3_2/algebra_polynomial_freyd_homology.ts` adds two deliberately separate
whole boundaries. `algebraPolynomialFreydChainPair(dNext,d)` validates the
middle presentation, computes the composite and zero morphism, and retains
their full presentation agreement whether it succeeds or fails.
`algebraPolynomialFreydHomologyAt(pair)` requires the positive agreement and
then composes the exact existing Freyd kernel, kernel-lift, and cokernel
operations. Its frozen result retains cycles, cycle embedding, boundary,
boundary reconstruction, homology, projection, and annihilation.

`algebraPolynomialFreydExactnessAt` compares that selected projection with
zero. Success additionally retains the computed epimorphism witness for the
boundary; failure retains the negative agreement without pretending to have
an epic map. Five focused tests cover invalid endpoints, a retained non-chain
pair, the nontrivial exact multiplication-by-`x`/quotient sequence, a valid
nonexact zero pair, and determinism. Root typecheck and focused lint pass.

## Implemented Categorical Homology Operations

`algebra_polynomial_freyd_homology_reference_operations.ts` defines stable
ring-scoped schemas, canonical whole-result serialization, and native
chain-pair, homology, and exactness operations.
`algebra_polynomial_freyd_homology_category.ts` extends the unchanged
operational Freyd Abelian category with one primitive chain-pair method and
derived homology/exactness methods. Homology planning retains the inherited
kernel, kernel-lift, and cokernel prerequisites; exactness retains the
epimorphism capability prerequisite.

The retained categorical program uses two unary nodes supported by the
existing IR: `pair → homology → exactness`. Both nodes lower to the native
reference engine, and graph outputs serialize byte-for-byte identically with
direct category execution. Three categorical tests cover planning traces,
direct/graph agreement, inherited Abelian methods, and the whole chain-pair
operation. Together with the five native tests, root typecheck and focused
lint pass. No derived-callback inlining or homology-specific IR syntax was
added.

## Baseline And Validation Policy

Use proportional, bounded checks. Do not run repository-wide TypeScript,
kernel, book, print, package, or release aggregates merely for reassurance.

### Planning and audit

- inspect exact staged/unstaged diffs and all worktrees;
- verify baseline ancestry and branch identity;
- run workspace validation;
- locate owners and consumers with `rg`;
- check only the relevant completed complex, Freyd Abelian, homological, and
  proof–CAS suites;
- check the relevant Lambdapi owners/reviewers with each target bounded to 90
  seconds; and
- record warning/LHS/catalog/health baselines before formal changes.

### TypeScript implementation

- root typecheck and affected-file lint;
- focused positive, negative, endpoint, foreign-ring, and determinism tests;
- direct operation, method planner, compiler, graph, and reference-engine
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

- injected deterministic adapter test first;
- installed external process remains opt-in and non-authoritative;
- mismatch remains observable; and
- native/formal execution never depends on the external CAS.

## Rejection Signals

Refine or reject a candidate when it:

- represents chain laws or exactness only by Booleans;
- asks users to hand-write chain-map squares instead of deriving/adopting them;
- assumes quotient-path decoding;
- postulates a homology object or induced map without the factor operations;
- duplicates kernels, cokernels, identity, composition, or Freyd quotient
  owners;
- treats the field-linear reference model as general polynomial authority;
- requires equality of selected image/kernel objects before computation;
- caps a whole construction required for functorial action;
- introduces a special-purpose categorical AST instead of the retained IR;
- adds broad hot-head runtime rewrites; or
- depends on an unrelated or orthogonal worktree.

## Completion Boundary

The goal is complete only when:

- generic one-degree homology is internally derived from selected
  kernels/cokernels;
- exactness is witness-rich and computational;
- nontrivial polynomial Freyd homology computes with all agreements retained;
- a bounded-complex consumer and one induced homology map work;
- one categorical homology program lowers and agrees with direct execution;
- the witnessed formal homology boundary checks without a quotient decoder;
- proof–CAS replays the actual operations and adopts the selected equations;
- field/Singular differential evidence remains non-authoritative;
- every rule/unifier, if any, has full SOP evidence;
- focused tests, typecheck, lint, formal reviewers, warnings, audits, catalog,
  health, and standing authorities are synchronized; and
- every ledger row is implemented, rejected with durable evidence, or
  explicitly deferred behind a concrete prerequisite.

The goal does not complete merely because the older field-linear homology
tests pass or because a homology object can be named.

## Deliberate Non-Goals

- arbitrary quotient-path decoding or choice;
- a closed formal polynomial Freyd `AbelianCategory` claim;
- connecting morphisms or long exact homology sequences;
- chain homotopies, quasi-isomorphisms, or derived-category localization;
- unbounded complexes, bicomplexes, DG categories, spectral sequences, or
  spectral algebraic geometry;
- varying-ring/semilinear Čech complexes or Čech cohomology;
- GAP/CAP API compatibility or CompilerForCAP AST recovery;
- parser, hosted service, package publication, push, merge, or release; and
- integration of path-cubical/global-strictness work.

## Sources And Design References

- completed Freyd–Abelian plan:
  `docs/TYPESCRIPT_EMDASH_FREYD_ABELIAN_COMPUTATION_PLAN.md`;
- completed bounded-free-complex plan:
  `docs/TYPESCRIPT_EMDASH_FORMAL_BOUNDED_FREE_COMPLEXES_PLAN.md`;
- focused CAS/CAP-aware architecture:
  `docs/TYPESCRIPT_EMDASH_FOCUSED_CAS_AND_CATEGORICAL_ENGINE_PLAN.md`;
- proof–CAS delegation architecture:
  `docs/TYPESCRIPT_EMDASH_PROOF_CAS_DELEGATION_PLAN.md`;
- active formal owners under `emdash2/`; and
- local CAP/homalg/Singular reference clones recorded by the completed CAS
  plans.

These sources guide decomposition and differential checks. Active code,
focused diagnostics, and repository SOP remain implementation authority.

## Persistent `/goal` Launch Prompt

Implement `TS-EMDASH-FREYD-HOMOLOGY-COMPUTATION` in
`/home/user1/emdash1-freyd-homology-v1` on
`goal/freyd-homology-computation-v3.2`, delegating every evolving owner audit,
generic chain-pair/homology/exactness formulation, native whole result,
categorical-program/lowering result, bounded-complex adapter, formal witnessed
construction, functorial homology result, proof–CAS consumer, differential,
warning classification, validation result, checkpoint, and completion
condition to this living plan. Preserve baseline
`4acef747d4b80e92c5c653e0b6635e6817a9c909` as comparison evidence. Preserve
whole universal-construction owners, explicit raw agreements, selected
weak-kernel nonuniqueness, generic identity/composition ownership,
backend-neutral categorical lowering, and the existing Freyd quotient
architecture. Follow root/nested persistent-goal and Lambdapi SOP; keep every
Lambdapi target bounded to 90 seconds; avoid unrelated aggregates; make only
local validated checkpoint commits after synchronizing the exact staged diff
and ledger. Do not push, merge, publish, release, create a PR, amend, rebase,
reset, rewrite history, delete branches, or remove worktrees. Do not claim
arbitrary quotient effectiveness or begin connecting morphisms, long exact
sequences, derived categories, spectral sequences, or orthogonal cubical/
strictness integration. The goal completes only when every scoped row is
implemented, rejected with durable evidence, or explicitly deferred behind a
concrete prerequisite and all affected authorities are synchronized.
