# TypeScript/emdash Focused CAS And Categorical Engine Plan

Date: 2026-08-30

Plan-ID: `TS-EMDASH-FOCUSED-CAS`

Status: living architecture and implementation ledger; computation-first and
CAP-aware design reviewed; dedicated implementation branch/worktree created;
`CAS-CONTRACT-1A` and `CAS-GRAPH-1B` implemented and proportional-green;
`CAS-EXACT-2A` is the next dependency-ready implementation row.

Baseline: `9edbdb2a929858f6d4091d475b750459dec8a681`

Branch: `goal/focused-cas-categorical-engine-v3.2`

Worktree: `/home/user1/emdash1-focused-cas-v1`

## Purpose

This plan governs a focused computer-algebra system for emdash, implemented
progressively in TypeScript and designed around the computational needs of
commutative algebra, algebraic geometry, homological algebra, and later
derived or spectral algebraic geometry.

The CAS is a useful computational system in its own right. The emdash proof
assistant is one consumer of its results. Logical certification is available
where useful, but it is not the organizing principle and must not block
ordinary computation or distort the CAS object model.

The plan also reserves the architectural boundary needed to subsume the
essential CAP/homalg design:

- a focused algebra engine supplies efficient primitive computations;
- algorithmic category theory forms a staged high-level programming layer;
- categorical doctrines, constructors, and towers specialize into explicit
  algebraic computation graphs; and
- a compiler removes categorical representation overhead before execution.

The first implementation priority remains exact arithmetic, polynomials,
ideals, matrices, and modules. CAP-style categorical programming is a later
layer and is not a prerequisite for adding or multiplying two polynomials.

## Authority And Relationship To Existing Plans

This is a new product and implementation plan. It does not reopen or replace:

- the active Lambdapi mathematical authority under `emdash2/`;
- the TypeScript explicit-Core/checker boundary recorded in
  `docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`;
- the proof-assistant and goal-graph plan;
- the TypeScript structures/classes/instance-synthesis plan; or
- the systematic v3.2 transfer and scale plans.

The focused CAS is initially an ordinary TypeScript computational library.
It must not silently add CAS evaluation to Core conversion, reuse the retired
category-specific TypeScript prototype as authority, or treat an operational
capability as mathematical structure evidence.

The current `CoreCategoricalProgram` facade is also not this plan's retained
categorical-computation IR. Its callbacks intentionally lower immediately to
explicit logical Core and are not retained as executable semantic state. The
CAS categorical-program layer will be separate and will retain a typed graph
for specialization and optimization.

## Governing Principle

> Emdash should own a focused algebraic computation engine whose objects and
> operations naturally match its formal algebraic geometry. Logical
> verification should be available where useful, but it should neither define
> the CAS architecture nor block usable computation.

The long-term hourglass is:

```text
emdash semantic mathematics
omega-categories, functors, universal properties, algebraic geometry
                    |
                    | optional computational realization
                    v
computable categorical programming layer
doctrines, categories, functors, constructors, towers
                    |
                    | specialization and compilation
                    v
algebraic computation graph
polynomials, matrices, modules, complexes, ideals
                    |
                    | execution
                    v
AlgebraEngine
TypeScript | WASM/native | Singular oracle | CAP/homalg oracle
```

## Primary Computation Flow

```text
emdash or TypeScript mathematical object
                 |
                 v
        computational presentation
                 |
                 v
       typed algebraic computation plan
                 |
                 v
  +-------------------------------------+
  | AlgebraEngine                       |
  |                                     |
  | - native TypeScript reference       |
  | - future optimized/WASM engine      |
  | - Singular/Macaulay2 oracle adapter |
  | - CAP/homalg categorical oracle     |
  | - remote or experimental engine     |
  +-------------------------------------+
                 |
                 v
         structured computed result
                 |
       +---------+----------+
       |         |          |
       v         v          v
 further CAS   display/   optional emdash
 computation   caching    logical adoption
```

The stable result is useful mathematical data, for example:

- a Groebner basis;
- change-of-generators matrices;
- normal forms and remainders;
- syzygy matrices;
- module presentations;
- chain complexes and free resolutions;
- kernel, image, and cokernel presentations;
- localization maps;
- Cech complexes;
- homology, Tor, Ext, and Hilbert data; and
- the structural maps relating all these objects.

Some outputs can also serve as proof certificates. That is secondary. A
change-of-generators matrix is retained primarily because later algorithms
need it.

## Computation Adoption Modes

The CAS and logical layers must distinguish four modes:

| Mode | Meaning |
| --- | --- |
| data | a computed polynomial, matrix, module, complex, chart, or other value; no theorem claim |
| trusted computation | a computed predicate or result may close a goal through an explicitly marked trusted declaration |
| checked computation | optional reconstruction or verification produces an ordinary emdash proof |
| definitional computation | one small, total, deterministic algorithm participates directly in evaluation/conversion |

The default CAS workflow is data and, where explicitly requested, trusted
computation. Checked computation is an optional adapter. Definitional
computation is limited to deliberately reviewed small algorithms.

Even a native TypeScript CAS does not imply that heavyweight algorithms
belong in Core conversion. Groebner bases, saturation, large syzygies, free
resolutions, homology, Ext/Tor, and spectral-sequence propagation remain
explicit computations. This protects predictable performance, cancellation,
caching, diagnostics, and evolvability independently of proof trust.

## Computational Object Model

The public computational model follows a restrained parent/element design:

```ts
interface AlgebraParent {
    readonly id: ParentId;
    readonly kind: ParentKind;
}

interface AlgebraElement<P extends AlgebraParent> {
    readonly parent: P;
}
```

Planned parents include:

```text
IntegerRing
RationalField
PrimeField(p)
FiniteFieldExtension
PolynomialRing(base, variables, monomial order)
QuotientRing(parent, relations)
LocalizationRing(parent, multiplicative data)
FreeModule(ring, rank)
PresentedModule(generators, relations)
ChainComplex(category, bounds)
```

Required invariants:

- every element carries or references its parent;
- incompatible parents are rejected unless a selected canonical coercion
  exists;
- canonical coercions may be implicit;
- general conversions and chosen isomorphisms are explicit;
- parent identities and portable structural encodings are stable;
- public values and portable artifacts are immutable;
- algorithms may use private mutable workspaces;
- exact arithmetic is the default; and
- approximate values carry quality, precision, and error information.

The active universal-property-first `CommRingPolynomialAlgebra` remains
unchanged. A CAS `PolynomialRing` is a concrete computational presentation
alongside it, not a replacement. Its semantic bridge can begin as operational
metadata and later acquire formal realization evidence without redesigning
the CAS.

## Operations, Algorithms, And Engines

Three notions remain separate:

```text
mathematical operation
implementation algorithm
engine capability
```

For example:

```text
operation: kernel(matrix)

algorithms:
  - row reduction over a field
  - Smith normal form over a PID
  - Groebner syzygies over a polynomial ring
```

The primary interfaces are conceptually:

```ts
interface AlgebraOperation<I, O> {
    readonly id: OperationId;
    readonly input: RuntimeSchema<I>;
    readonly output: RuntimeSchema<O>;
}

interface AlgebraEngine {
    support<I, O>(
        operation: AlgebraOperation<I, O>,
        input: I
    ): EngineSupport;

    compute<I, O>(
        operation: AlgebraOperation<I, O>,
        input: I,
        context: ComputationContext
    ): Promise<Computed<O>>;
}
```

The exact implementation may refine these sketches, but must preserve:

- versioned operation identities;
- input and output validation independent of an engine;
- deterministic capability inspection;
- bounded execution context, progress, and cancellation;
- structured diagnostics;
- explicit algorithm identity;
- result quality and assumptions;
- portable results separate from session-only state; and
- no process, JSON, or external-CAS premise in the internal engine API.

In-process TypeScript, future WASM/native accelerators, and external oracles
are ordinary engines. JSON or process transport belongs only in external
adapters.

## Computed Results

The stable result is conceptually:

```ts
interface Computed<T> {
    readonly value: T;
    readonly quality:
        | "exact"
        | "probabilistic"
        | "heuristic"
        | "partial";
    readonly engine: EngineIdentity;
    readonly algorithm: AlgorithmIdentity;
    readonly assumptions: readonly ComputationalAssumption[];
    readonly diagnostics: readonly ComputationDiagnostic[];
    readonly reusable: readonly IntermediateArtifact[];
}
```

For a Groebner computation, reusable results may include leading monomials,
transformation matrices, reduction information, discovered syzygies, and
Hilbert data. Portable artifacts retain mathematical results; in-memory
sessions may additionally retain optimized mutable state.

## Explicit Computation Graph

Every operation must be representable as a typed computation node. Direct
execution is a convenience lowering of a one-node graph, not the only
semantics.

The graph boundary exists from the first tranche so later work can support:

- dependency-aware execution;
- retained intermediate results;
- structural caching;
- common-subexpression elimination;
- batching and fusion;
- deterministic cost planning;
- independent-node parallelism;
- partial-result recovery;
- external-oracle comparison; and
- lowering from categorical programs.

The graph is backend-neutral and portable. Engine sessions and mutable
algorithm state are not serialized into it.

## CAP And homalg Design Inventory

The reviewed CAP/homalg functionality relevant to this plan includes:

| Concern | Essential content to preserve |
| --- | --- |
| categories | runtime objects, morphisms, source/range, identity, composition, equality/congruence, selected two-cell support |
| doctrines | structured families such as preadditive, additive, Abelian, monoidal, Cartesian, and finite-complete categories |
| operations | signatures for kernels, cokernels, lifts, products, pullbacks, tensor products, images, homology, and related constructions |
| derived methods | multiple implementations of one operation from prerequisite operations, with applicability and cost |
| logic propagation | doctrine-specific operational consequences and property propagation |
| universal constructions | object, structural map, lift/colift, functoriality, and with-given variants |
| category constructors | opposite, product, additive closure, Freyd, slice, functor, quotient, stable-poset, and related constructors |
| towers | composable category constructors between doctrines |
| reinterpretation | a convenient public representation related to a tower that models it |
| compilation | resolve operations, inline derivations, infer data, erase wrapping, hoist/fuse, and lower to specialized primitives |
| applications | modules, generalized morphisms, complexes, spectral sequences, representations, sheaves, locales, and constructible sets |

The historical relationship is:

```text
ring and matrix normal-form algorithms
              |
              v
finitely presented modules
              |
              v
computable Abelian category
              |
              v
generic homological algorithms
              |
              v
complexes, resolutions, derived functors, spectral sequences
```

homalg initially built this path relatively directly. CAP factors the middle
and upper layers into reusable categorical programming components. Emdash
will preserve the factorization while using the focused algebra engine as the
efficient substrate.

## Computable Categorical Programming Layer

### Doctrine descriptors

Operational doctrine metadata is conceptually:

```ts
interface DoctrineDescriptor {
    readonly id: DoctrineId;
    readonly parents: readonly DoctrineId[];
    readonly operations: readonly CategoryOperationId[];
    readonly dual?: DoctrineId;
}
```

Initial doctrine targets are:

```text
Category
PreadditiveCategory
AdditiveCategory
PreAbelianCategory
AbelianCategory
CartesianCategory
MonoidalCategory
ClosedMonoidalCategory
```

This is runtime programming metadata, not automatically LF evidence. The LF
class-schema and instance machinery may later help connect formal structures
to computational profiles, but operational capability availability remains a
separate concern.

### Computable categories

```ts
interface ComputableCategory {
    readonly id: RuntimeCategoryId;
    readonly doctrine: DoctrineDescriptor;
    readonly objectSchema: RuntimeSchema<unknown>;
    readonly morphismSchema: RuntimeSchema<unknown>;
    readonly operations: CategoryOperationRegistry;
    readonly engineProfile: EngineProfile;
}
```

A computable category accounts for identity, composition, source/range,
morphism comparison or normalization, primitive and derived algorithms,
costs, caches, and an optional semantic link to emdash.

The first implementation is strict/set-level computational category theory.
It must not impose ordinary strict-category equality on the full emdash
omega-categorical semantics.

### Category constructors

```ts
interface CategoryConstructor {
    readonly id: CategoryConstructorId;
    readonly inputDoctrine: DoctrineConstraint;
    readonly outputDoctrine: DoctrineDescriptor;
    readonly lowering: ConstructorLoweringRules;
    readonly dual?: CategoryConstructorId;

    construct(input: ComputableCategory): ComputableCategory;
}
```

A constructor records object and morphism representations, boxing/unboxing,
lifted operations, underlying-operation lowering, associated functors,
compiler rules, and optional public reinterpretation.

Operation descriptors and constructors should record duals where appropriate.
The existing emdash opposite-category architecture is an opportunity to
generate dual runtime operations systematically instead of maintaining a
large duplicated mirror API.

### Retained categorical programs

Generic categorical algorithms build an explicit staged IR:

```ts
const homology = defineCategoricalProgram(
    "homology",
    AbelianCategory,
    program => {
        const cycles = program.kernel(program.input("d"));
        const boundaries = program.image(program.input("dNext"));
        return program.quotient(cycles, boundaries);
    }
);
```

The callback sees symbolic values and builds a graph. It does not execute the
computation and does not lower immediately to logical Core.

## Tower Compiler

CompilerForCAP must recover an enhanced syntax tree from arbitrary GAP
functions and dynamic method dispatch. Emdash should instead start from a
typed explicit IR:

```text
typed TypeScript builder
        |
        v
explicit CategoricalProgram IR
        |
        v
tower specialization
        |
        v
AlgebraComputationGraph
        |
        v
AlgebraEngine
```

Planned deterministic compiler passes are:

1. validate source/range and doctrine requirements;
2. resolve primitive versus derived categorical operations;
3. inline the selected derivation tree;
4. expand category constructors;
5. normalize opposite and dual structure;
6. compose representation and box/unbox maps;
7. eliminate inverse representation pairs;
8. recognize registered reinterpretations;
9. lower categorical operations to polynomial, matrix, and module operations;
10. perform common-subexpression elimination, hoisting, fusion, batching, and
    parallel scheduling;
11. select engine algorithms from deterministic capability and cost profiles;
    and
12. cache the compiled plan by program, tower, and engine-profile identity.

The compiler initially relies on executable equivalence tests and oracle
comparisons. Optional proof production may later validate selected lowering
rules without becoming a prerequisite for computation.

## Reinterpretation

Reinterpretation is a first-class computational boundary:

```ts
interface ComputationalReinterpretation<PublicObject, ModelObject> {
    readonly publicCategory: ComputableCategory;
    readonly modelingCategory: ComputableCategory;

    toModel(value: PublicObject): ModelObject;
    fromModel(value: ModelObject): PublicObject;

    readonly loweringRules: readonly RepresentationRewrite[];
}
```

The primary example is:

```text
public value:
    PresentedModule<R>

model:
    object of Freyd(AdditiveClosure(RingCategory(R)))
```

Users manipulate direct presentation matrices. Generic categorical algorithms
may use the tower. Compilation removes the Freyd/additive-closure wrappers and
produces direct matrix or syzygy computations.

## Whole Universal Constructions

CAP exposes separate kernel object, embedding, lift, functorial, and
with-given operations. Emdash should make the selected whole construction the
primary internal value and derive projections:

```ts
interface KernelConstruction<O, M> {
    readonly object: O;
    readonly embedding: M;
    lift(source: O, arrow: M): Promise<M>;
}
```

Fields may be lazy and memoized. This avoids recomputation and matches the
coherent whole-construction preference of the formal emdash architecture.

The same pattern applies to cokernels, products, coproducts, pullbacks,
pushouts, images, coimages, tensor products, and adjunction-derived
operations. CAP-compatible projection and with-given facades can be derived
when a consumer needs them.

## Focused Mathematical Roadmap

### Exact coefficient domains

Start with integers, rationals, prime fields, and exact sparse matrices.
Finite extensions follow later. JavaScript `number` is never used for exact
coefficients. The reference implementation begins with `bigint`-based exact
values and preserves an engine boundary for later WASM/native acceleration.

### Sparse multivariate polynomials

Implement canonical monomials, explicit monomial orders, immutable public
polynomials, mutable private builders, arithmetic, leading terms, reduction,
multivariate division, substitution, and polynomial maps.

### Ideals and quotient rings

Implement Buchberger as the clear reference algorithm, reduced bases, ideal
membership, change-of-generators matrices, elimination, sums, products,
intersections, saturation, radical membership, and quotient normal forms.
F4/F5-style optimization is later and does not change the public operation
contract.

### Direct geometry consumer

The first high-value end-to-end operation is:

```text
unimodularCombination([f1,...,fn])
  -> coefficients [a1,...,an]
  with sum_i ai*fi computationally equal to 1
```

The coefficients are the primary result. An emdash adapter can construct the
existing `CommRingUnimodularPresentation` and a Zariski-cover presentation.
Its law may initially be trusted computation and later checked without a CAS
redesign.

Nearby applications are basic-open intersections, cover refinements, affine
fiber products, quotient coordinate rings, scheme-theoretic intersections,
and elimination for images of affine morphisms.

### Modules and homological algebra

Use finite presentations and matrices to implement modules, morphisms,
kernels, images, cokernels, syzygies, free resolutions, complexes, homology,
derived tensor products, Tor, Ext, grading, shifts, and Hilbert data.

### Algebraic geometry

Build affine schemes and maps from presented rings, fiber products, closed and
basic-open subschemes, localization and overlap computations, finite affine
covers, Cech nerves/complexes, quasi-coherent modules, and computed gluing
maps.

### Derived and spectral preparation

Prepare graded-commutative rings/modules, chain complexes, DG algebras and
modules, simplicial modules and normalization, filtered complexes, exact
couples, spectral-sequence pages/differentials, and derived tensor/Hom from
explicit resolutions. General spectrum computation is not an early claim.

## CAP-Subsumption Validation Targets

### Target A: finitely presented modules

```text
RingCategory(R)
  -> AdditiveClosure
  -> FreydCategory
  -> reinterpret as PresentedModules(R)
```

Compile composition, kernel/cokernel, lift/colift, image/coimage, and homology
of a short complex into native matrix, Groebner, and syzygy operations.

### Target B: constructible algebraic geometry

Model the relevant tower:

```text
RingAsCategory
  -> AdditiveClosure
  -> Slice over tensor unit
  -> Poset
  -> StablePoset
  -> Opposite
  -> Differences
  -> Unions
```

Lower it to ideal sum/intersection/product/quotient, saturation, radical
equivalence, Zariski open/closed data, locally closed subsets, and Boolean
combinations of constructible sets.

### Target C: homological algorithms

Implement generic connecting morphisms, snake-lemma sequences, complexes,
bicomplexes, generalized morphisms, spectral-sequence pages and differentials,
induced filtrations, and derived tensor/Hom through resolutions.

## External Systems As Oracles

External systems are reference implementations, differential-testing oracles,
performance baselines, and temporary providers for not-yet-native operations.
They do not own the emdash object model.

The oracle strategy includes:

- randomized and curated differential testing;
- checking edge cases and conventions;
- comparing reduced canonical forms;
- measuring performance;
- generating hard examples; and
- inspecting intermediate matrices, bases, syzygies, and resolutions.

External adapters implement the same operation descriptors as native engines.
Their transport does not define the internal API.

## Reviewed Source Baseline

Temporary shallow research clones live outside the repository under
`/tmp/emdash-cas-source-review.AsHfvn`. They are reference evidence and are
never vendored or committed by this plan.

| Project | Reviewed revision or role |
| --- | --- |
| CAP_project | `d21dc5f5f420`; categories, operations, derivations, constructors, CompilerForCAP |
| homalg_project | `802993da0095`; matrices, external-ring dictionaries, modules, homological algorithms |
| CategoricalTowers | `ea383845f79e`; slice, functor, presheaf, quotient, locale, and Zariski towers |
| CapAndHomalg.jl | `fd1520e5fe12`; Julia compatibility/access layer over GAP packages and bundled tools |
| CAP_project.jl | `0a9b4b31289a`; mechanically transpiled Julia packages |
| CAP.jl | `386313a72649`; generated Julia CAP plus GAP-emulation layer |
| LeanM2 | `c51074d1a104`; Macaulay2-backed ideal-membership witness reconstruction |
| lp-tactic | `86634295a1fa`; engine registry and solver-independent checked result design |
| Lambdapi | `7adcf4f63ce9`; current Why3 tactic boundary |
| Singular | `11befc1bb663`; sparse checkout of `Singular`, `kernel`, `libpolys`, `factory`, and documentation for polynomial, standard-basis, reduction, and syzygy reference |
| Macaulay2 | `1a37f6fe95ba`; sparse checkout of the engine, language layer, and `Macaulay2Doc` for Groebner, quotient/remainder, change-matrix, and syzygy reference |
| Oscar.jl | `1d7ce77e9949`; sparse checkout of `src`, architecture documentation, and examples for parent/element and multi-engine algebraic interfaces |

Further shallow or sparse clones of Singular, Macaulay2, OSCAR, and relevant
algorithm implementations may be added under the same temporary reference
directory. Their exact revisions and inspected paths must be recorded here
when they influence a design or algorithm decision.

Important source-level findings:

- `CapAndHomalg.jl` is chiefly a Julia compatibility/access package around GAP
  implementations and `GapObj` values, not a clean native Julia categorical
  IR to copy.
- `CAP_project.jl` mechanically transpiles GAP packages and retains a
  GAP-emulation layer; this reinforces the value of an explicit
  language-neutral operation and tower IR.
- CompilerForCAP specializes a concrete category instance, resolves dynamic
  operations, rewrites an enhanced syntax tree, and precompiles functions.
  Emdash should preserve the specialization idea while avoiding recovery of a
  graph from arbitrary TypeScript source.

## Usability Priorities

Prioritize:

- direct TypeScript construction, with no parser prerequisite;
- readable mathematical pretty-printing;
- deterministic defaults;
- explicit parent/ring display;
- good coercion diagnostics;
- progress, cancellation, and resource budgets;
- persistent computation workspaces;
- structural caching;
- inspectable algorithm and derivation trees;
- conversion between display and sparse forms;
- AI-friendly typed operations;
- partial-result recovery after timeout;
- portable computed artifacts; and
- oracle comparison commands.

The intended surface should feel like mathematics:

```ts
const Qxy = polynomialRing(QQ, ["x", "y"]);
const { x, y } = Qxy.generators();

const I = ideal(Qxy, [
    x.pow(2).sub(y),
    y.pow(2).sub(x)
]);

const G = await compute(groebnerBasis, I);
const M = await compute(syzygyModule, G.value);
```

The same values may be consumed by a notebook, an AI tool, an emdash
elaborator adapter, or an optional proof-development adapter.

## Non-Goals And Guardrails

- Do not build a miniature SageMath without concrete emdash consumers.
- Do not organize the project around proof certificates or
  `EXTERNAL-CERT-11`.
- Do not make an external CAS the permanent default semantic owner.
- Do not use JavaScript `number` for exact arithmetic.
- Do not put heavyweight CAS algorithms into global Core conversion.
- Do not reuse the retired category-specific root prototype as v3.2
  authority.
- Do not overload the current immediate-lowering `CoreCategoricalProgram` with
  retained CAS execution state.
- Do not emulate GAP filters, globals, or dynamic dispatch as the emdash
  public architecture.
- Do not compile arbitrary TypeScript source by decompiling its AST; construct
  a typed computation graph explicitly.
- Do not conflate runtime `CanCompute`-style availability with mathematical
  doctrine evidence.
- Do not impose strict one-category computation on emdash's omega-categorical
  semantics.
- Do not require Julia, GAP, Singular, Macaulay2, Lambdapi, or a network
  service for the native reference engine.
- Do not publish, merge, push, or release from this goal without separate
  authorization.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `CAS-PLAN-0` | complete | reviewed design discussion and source audit | this living plan, branch/worktree identity, source baseline, architecture, decisions, validation, and launch prompt |
| `CAS-CONTRACT-1A` | complete; proportional-green at `46b8fda` | `CAS-PLAN-0` | browser-safe immutable operation, engine, support, result-quality, execution-context, diagnostic, and reusable-artifact contracts; ten focused tests, workspace check, affected lint, typecheck, and diff hygiene green; no algorithm, process, logical-Core, or public-package dependency |
| `CAS-GRAPH-1B` | complete; proportional-green at `d6e2e00` | `CAS-CONTRACT-1A` | typed backend-neutral input/node/output computation graph, immutable reconstruction, bounded validation, topology-only stable JSON, cancellation, exact-node diagnostics, and sequential direct-execution lowering; eleven focused graph tests plus the ten predecessor tests green |
| `CAS-EXACT-2A` | in progress | `CAS-GRAPH-1B` | exact integer/rational domains using `bigint`, normalization, arithmetic, serialization, and strict negatives |
| `CAS-POLY-2B` | pending | `CAS-EXACT-2A` | parent-aware sparse multivariate polynomials, monomial orders, arithmetic, substitution, and division |
| `CAS-ENGINE-2C` | pending | `CAS-POLY-2B` | native TypeScript reference engine executes selected exact and polynomial graph nodes with limits/cancellation |
| `CAS-IDEAL-3A` | pending | `CAS-ENGINE-2C` | ideals, Buchberger reference implementation, reduction, membership, reduced bases, and retained transformations |
| `CAS-ZARISKI-3B` | pending | `CAS-IDEAL-3A` | unimodular-combination computation and optional adapter to current Zariski-cover presentation |
| `CAS-MATRIX-4A` | pending | `CAS-EXACT-2A`, `CAS-ENGINE-2C` | exact matrices and selected row/column algorithms with explicit orientation conventions |
| `CAS-MODULE-4B` | pending | `CAS-IDEAL-3A`, `CAS-MATRIX-4A` | free and finitely presented modules, morphisms, kernels/cokernels, and syzygies |
| `CAS-CATEGORY-5A` | pending | `CAS-GRAPH-1B`, representative algebra values | minimal strict computable-category runtime, ring-as-category, matrix/free-module category, primitive/derived registry |
| `CAS-DOCTRINE-5B` | pending | `CAS-CATEGORY-5A` | preadditive, additive, pre-Abelian, and Abelian doctrine descriptors with dual metadata |
| `CAS-TOWER-5C` | pending | `CAS-DOCTRINE-5B` | Opposite, AdditiveClosure, Freyd, and reinterpretation descriptors with retained lowering data |
| `CAS-COMPILER-6A` | pending | `CAS-TOWER-5C` | retained categorical-program IR and first specialization/lowering passes to algebra graph |
| `CAS-FREYD-6B` | pending | `CAS-COMPILER-6A`, `CAS-MODULE-4B` | compiled Freyd/AdditiveClosure presentation agrees operationally with direct `PresentedModule` computations |
| `CAS-HOMOLOGICAL-7A` | pending | `CAS-FREYD-6B` | complexes, homology, connecting morphism, initial generalized-morphism and resolution algorithms |
| `CAS-CONSTRUCTIBLE-8A` | pending | `CAS-ZARISKI-3B`, `CAS-COMPILER-6A` | selected slice/poset/stable-poset/opposite/difference/union tower lowered to ideal and saturation operations |
| `CAS-ORACLE-9A` | pending | one native representative consumer | opt-in Singular/Macaulay2/CAP-homalg differential oracle with no public semantic authority |
| `CAS-FORMAL-BRIDGE-10` | deferred | concrete formal consumer | selected computational realization, trusted-computation marker, or checked-proof adapter; not a CAS prerequisite |

No later row may be advanced merely to keep the goal active. Each row requires
a concrete consumer, bounded implementation, focused positive/negative tests,
and a synchronized ledger decision.

## First Bounded Tranche: `CAS-CONTRACT-1A`

The first implementation tranche owns only contracts and validation:

- stable operation, engine, and algorithm identities;
- immutable runtime schemas or validators;
- exact support outcomes and diagnostics;
- execution limits and cancellation hooks without a platform dependency;
- computed quality, assumptions, diagnostics, and reusable artifacts;
- independent validation of engine outputs;
- no arithmetic algorithm;
- no graph yet beyond interfaces needed by the next row;
- no process, filesystem, network, JSON-RPC, Lambdapi, or CAS dependency;
- no public package export until the focused contract is reviewed; and
- no logical Core constructor or checker change.

Required focused evidence:

- valid exact result construction;
- unsupported/invalid operation or engine identities rejected;
- malformed quality/diagnostic/artifact data rejected;
- immutable snapshots cannot be mutated through retained inputs;
- engine support is inspectable without executing the operation;
- an engine result with a foreign operation identity is rejected;
- cancellation and budget data remain management metadata; and
- browser-safe dependency audit.

This first tranche is an isolated contributor-only module with no public
package export. Its proportional gate is the focused algebra-engine suite,
affected-file lint, root typecheck, and workspace check. By explicit user
direction on 2026-08-30, it does not run the complete TypeScript aggregate or
other repository-wide checks over untouched features. An initially started
`check:ts` run completed workspace/typecheck/lint and then spent about nineteen
minutes in the historical aggregate test catalog without diagnostics; it was
explicitly cancelled when the scope policy was clarified and is not claimed
as green or as a product failure. Kernel, book, print, package-release, and
cross-layer aggregates are also outside this row.

## Decision Ledger

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-CAS-001` | accepted | The primary abstraction is `AlgebraEngine`, not `CertificateBackend`. |
| `D-CAS-002` | accepted | The native TypeScript reference engine is the intended default; external CAS systems are oracle engines and temporary coverage providers. |
| `D-CAS-003` | accepted | Structured computed results, not proof certificates, form stable interchange. |
| `D-CAS-004` | accepted | Heavy algorithms remain explicit computations outside Core conversion even when written in TypeScript. |
| `D-CAS-005` | accepted | Parent/element identity and canonical-coercion discipline are foundational usability requirements. |
| `D-CAS-006` | accepted | Mathematical operation, implementation algorithm, and engine capability are separate identities. |
| `D-CAS-007` | accepted | Every operation is representable as a typed computation graph node from the first architecture tranche. |
| `D-CAS-008` | accepted | CAP-style algorithmic category theory is a staged layer above the algebra graph, not a replacement for the focused algebra engine. |
| `D-CAS-009` | accepted | Runtime doctrine/capability metadata is separate from LF class evidence and formal mathematical authority. |
| `D-CAS-010` | accepted | Categorical algorithms retain explicit IR; arbitrary TypeScript/GAP AST recovery is not the architecture. |
| `D-CAS-011` | accepted | Reinterpretation and box/unbox elimination are first-class compiler concepts. |
| `D-CAS-012` | accepted | Whole universal constructions are primary; CAP-style projections and with-given operations are derived facades. |
| `D-CAS-013` | accepted | The first CAP-subsumption target is finitely presented modules via `Freyd(AdditiveClosure(RingCategory(R)))`. |
| `D-CAS-014` | accepted | The first algebraic-geometry tower target is the constructible-set/Zariski tower lowered to ideal and saturation operations. |
| `D-CAS-015` | accepted | CapAndHomalg.jl and transpiled CAP Julia packages are oracle/reference inputs, not public emdash object models. |
| `D-CAS-016` | accepted | Proof certification is optional; explicit data/trusted/checked/definitional modes remain distinguishable. |
| `D-CAS-017` | accepted | The initial implementation begins with the portable computation contract before exact arithmetic or categorical doctrines. |
| `D-CAS-018` | accepted | Early isolated CAS rows use proportional focused validation only; repository-wide long aggregates over untouched features require a genuinely affected boundary or an explicit request. |
| `D-CAS-019` | accepted | The user explicitly authorizes validated local checkpoint commits on this dedicated goal branch as work progresses; push, merge, publication, release, and history rewriting remain unauthorized. |
| `D-CAS-020` | accepted | Graph v1 serializes topology, operation/schema identities, preferred algorithms, and named outputs; runtime input values remain separate execution data. |
| `D-CAS-021` | accepted | Graph v1 uses declared topological order and one selected engine, retaining every node result; optimization, engine routing, caching, batching, and parallel scheduling remain later rows. |
| `D-CAS-022` | accepted | Graph construction and reconstruction require exact schema-identity agreement across edges; no implicit computational coercion is invented at the graph layer. |

## `CAS-CONTRACT-1A` Result

The first contract is implemented in `src/v3_2/algebra_engine.ts` and exposed
only through the contributor `src/v3_2/index.ts` barrel. It is deliberately
absent from the distributable package barrels.

Semantic checkpoint: `46b8fda` (`cas: add algebra engine contracts`).

The implementation provides:

- role-distinguished operation, engine, algorithm, and schema identities;
- value-specific runtime schema normalization;
- immutable operation and engine definitions;
- supported/unsupported capability inspection independent of execution;
- bounded execution, cancellation, and progress management metadata;
- exact/probabilistic/heuristic/partial result quality;
- assumptions, diagnostics, and schema-validated reusable artifacts;
- one normalization of each computation input before support and execution;
- validation that output operation, engine, and algorithm identities agree
  with the inspected support surface; and
- normalized immutable output detached from engine-owned mutable candidates.

Focused evidence in `tests/v3_2_algebra_engine_tests.ts` covers ten positive
and negative cases. Final proportional commands on the checkpoint candidate:

```text
./scripts/pnpmw run workspace:check
./scripts/pnpmw exec node --require ts-node/register --test tests/v3_2_algebra_engine_tests.ts
./scripts/pnpmw exec eslint src/v3_2/algebra_engine.ts src/v3_2/index.ts tests/v3_2_algebra_engine_tests.ts tests/main_tests.ts
./scripts/pnpmw run typecheck
git diff --check
```

All pass. The initially started repository aggregate was explicitly cancelled
under `D-CAS-018` and is not part of the acceptance evidence.

## `CAS-GRAPH-1B` Result

The first graph profile is implemented in `src/v3_2/algebra_graph.ts` and is
also confined to the contributor barrel. It provides:

Semantic checkpoint: `d6e2e00` (`cas: add algebra computation graphs`).

- typed graph-input and node-output tokens scoped to one builder identity;
- globally distinct input/node IDs and distinct named-output IDs;
- exact schema checks on every edge;
- optional preferred algorithms retained per node;
- one-shot builders producing independently reconstructed immutable graphs;
- topological-reference validation and explicit graph-size ceilings;
- deterministic topology-only JSON with no runtime values or callbacks;
- exact input-set validation;
- graph-level pre-node cancellation;
- sequential lowering through `computeAlgebraOperation`;
- retained immutable node results and named outputs; and
- graph-node diagnostics wrapping the exact underlying engine error.

Focused evidence in `tests/v3_2_algebra_graph_tests.ts` covers eleven positive
and negative graph cases. The graph suite and the ten predecessor contract
tests pass together, followed by affected-file lint, root typecheck, and diff
hygiene. No aggregate, kernel, package, browser, print, or book check is
required by the scoped policy.

## Validation Policy

Documentation-only plan changes require exact diff, Markdown/link hygiene,
and no unrelated aggregate.

For TypeScript implementation rows:

1. run `./scripts/pnpmw run workspace:check` when workspace assumptions are
   involved;
2. run the nearest focused tests during iteration;
3. run root typecheck and lint for the affected files;
4. run browser and package checks only when their exported boundary changes;
5. carry forward recent aggregate evidence for untouched boundaries and do
   not run `check:ts` merely because a focused test was wired into the explicit
   root runner; and
6. run `check:ts` only when a genuinely shared generic/runtime/package
   boundary is affected or the user explicitly requests it; and
7. run `check:all`, Lambdapi, kernel, print, or book gates only at an actually
   affected cross-layer boundary.

External oracle tests are opt-in, version-pinned, and never part of the native
engine's ordinary correctness or availability contract.

## Git And Persistent-Goal Policy

The dedicated branch/worktree and validated local progress checkpoint commits
are explicitly authorized by the user. No push, merge, publication, release,
history rewrite, branch/worktree deletion, or cleanup is authorized.

Before every continuation:

- reread root guidance and this plan;
- inspect all worktrees, branch, `HEAD`, ancestry, staged and unstaged state;
- preserve unrelated work;
- relocate owners and consumers with `rg`;
- select only one dependency-ready row; and
- update this ledger whenever evidence changes the architecture.

## Persistent Goal Launch Prompt

```text
Continue the focused TypeScript CAS and computable-categorical engine goal in
/home/user1/emdash1-focused-cas-v1 on
goal/focused-cas-categorical-engine-v3.2.

Treat docs/TYPESCRIPT_EMDASH_FOCUSED_CAS_AND_CATEGORICAL_ENGINE_PLAN.md as the
living plan and delegate all evolving implementation detail, row selection,
validation, and architectural decisions to that file. Preserve the
computation-first AlgebraEngine baseline and the staged CAP/homalg-aware
categorical layer. Start or resume exactly one dependency-ready ledger row,
run proportional validation, and keep the plan synchronized with accepted,
rejected, or deferred evidence.

The user authorizes this dedicated branch/worktree, in-scope edits, and local
validated progress checkpoint commits. Pushes, merges, publication, releases,
history rewriting, and cleanup remain unauthorized unless separately
requested. Do not modify main or any other worktree. Do not treat proof
certification, Lambdapi, or an external CAS as a prerequisite for native
computation.
```
