# TypeScript/emdash Focused CAS And Categorical Engine Plan

Date: 2026-08-30

Plan-ID: `TS-EMDASH-FOCUSED-CAS`

Status: living architecture and implementation ledger; computation-first and
CAP-aware design reviewed; dedicated implementation branch/worktree created;
`CAS-CONTRACT-1A` through `CAS-MATRIX-4A` implemented and
proportional-green; `CAS-MODULE-4B1` and `CAS-CATEGORY-5A` are implemented and
focused-green; `CAS-DOCTRINE-5B`, `CAS-TOWER-5C`, and `CAS-COMPILER-6A` are
implemented and focused-green; `CAS-FREYD-6B` is implemented and
proportional-green; `CAS-HOMOLOGICAL-7A` is complete and proportional-green;
the `CAS-MODULE-4B2A` through `4B2C` tranches are implemented and proportional-green,
while the larger `CAS-MODULE-4B2` row remains in progress and
`CAS-CONSTRUCTIBLE-8A` remains independently dependency-ready.

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
| `CAS-EXACT-2A` | complete; proportional-green at `36dc108` | `CAS-GRAPH-1B` | stable parent/element base; canonical bigint-only integers and reduced rationals; arithmetic, order, Euclidean division, gcd, powers, text/JSON serialization, runtime schemas, and immutable operational domains; twelve exact tests and all 33 focused CAS tests green |
| `CAS-POLY-2B` | complete; proportional-green at `7b6b929` | `CAS-EXACT-2A` | coefficient-polymorphic parent-aware sparse multivariate polynomials; lex/grlex/grevlex, canonicalization, arithmetic, powers, substitution, stable serialization, runtime schema, and field-only ordered division; thirteen polynomial tests and all 46 focused CAS tests green |
| `CAS-ENGINE-2C` | complete; proportional-green at `765aa32` | `CAS-POLY-2B` | native in-process TypeScript registry with multiple deterministic algorithms per exact operation contract; selected integer/rational and ring-specific polynomial operations, direct/graph execution, fuel, cancellation, progress, metadata, and output limits; ten engine tests and all 56 focused CAS tests green |
| `CAS-IDEAL-3A` | complete; proportional-green at `58f51f2` | `CAS-ENGINE-2C` | ordered polynomial ideals; deterministic monic Buchberger basis, retained generator transformations, reduced-basis postpass, positive/negative membership decomposition, schemas/serialization, bounded cancellation, native operations, and graph pipeline; eleven ideal tests and all 67 focused CAS tests green |
| `CAS-ZARISKI-3B` | complete; proportional-green at `ebbe15f` | `CAS-IDEAL-3A` | whole unimodular result retaining ideal/basis/membership/coefficients/combination/remainder; positive-only computational finite basic-open cover, schemas/serialization, native operations, and graph pipeline; formal adapter explicitly deferred; nine tests and all 76 focused CAS tests green |
| `CAS-MATRIX-4A` | complete; proportional-green at `442cbff` | `CAS-EXACT-2A`, `CAS-ENGINE-2C` | structural exact matrix spaces; immutable row-major arithmetic, transpose, composition, RREF with left transformation, column-kernel basis, schemas/serialization, field/limit/cancellation gates, native operations, and transpose graph; nine tests and all 85 focused CAS tests green |
| `CAS-MODULE-4B1` | complete; focused-green at `707a7da` | `CAS-MATRIX-4A` | field-linear free/presented modules, relation-witnessed morphisms and composition, quotient projection/section realization, free kernels, presented cokernels, and matrix syzygies; seven module and nine affected matrix tests green |
| `CAS-MODULE-4B2` | in progress; `4B2A` `ecf1b97`, `4B2B` `96dad7f`, `4B2C` `499aea5` green | `CAS-IDEAL-3A`, `CAS-MODULE-4B1` | module orders/Buchberger/membership, Schreyer syzygies, presented polynomial modules, quotient normal forms, and bounded recursive free resolutions complete; native graph operations remain |
| `CAS-CATEGORY-5A` | complete; proportional-green at `64b4c7c` (core `90cfca0`) | `CAS-GRAPH-1B`, `CAS-MODULE-4B1` | strict category shell, weighted primitive/derived registry, ring-as-one-object category, and presented-field-module category with primitive whole kernels/cokernels and derived object projections; four category and sixteen affected module/matrix tests green |
| `CAS-DOCTRINE-5B` | complete; focused-green at `02ac3d0` | `CAS-CATEGORY-5A` | explicit Category/Preadditive/Additive/Pre-Abelian/Abelian hierarchy, involutive doctrine/role duality, inherited capability roles, plannability-based qualification and missing-role reports; four doctrine and four affected category tests green |
| `CAS-TOWER-5C` | complete; focused-green at `dd910b0` | `CAS-DOCTRINE-5B` | validated constructor/tower/lowering/reinterpretation descriptors, executable opposite category, AdditiveClosure/Freyd/CoFreyd metadata, module-tower consumer and invalid-chain checks; five tower and fifteen affected doctrine/category/module tests green |
| `CAS-COMPILER-6A` | complete; proportional-green at `c28da8f` | `CAS-TOWER-5C` | scoped retained categorical-program IR, method-resolution trace, explicit schema-preserving category-to-algebra bindings, tower-rule retention, graph lowering and native execution; three compiler and thirty affected tests green |
| `CAS-FREYD-6B` | complete; proportional-green at `2f26a59` | `CAS-COMPILER-6A`, `CAS-MODULE-4B1` | native whole module kernel/cokernel operations, concrete Freyd/AdditiveClosure field-module model, direct-presentation reinterpretation, schema-preserving compiler bindings, retained reinterpretation rule, and structural agreement with direct `PresentedModule` computations; three Freyd and forty affected tests green |
| `CAS-HOMOLOGICAL-7A` | complete; `7A1` `66ed5a8`, `7A2` `8b97bad`, `7A3` `5f22b08`, `7A4` `3961bc5`, `7A5` `052032a`, `7A6` `ab68a11` green | `CAS-FREYD-6B` | quotient-aware universal operations, bounded complexes, whole/functorial/connecting homology, initial generalized spans, field resolutions, and native graph operations complete; broader representations and polynomial resolutions remain separately gated |
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
| `D-CAS-023` | accepted | Exact integer/rational values store only `bigint`; constructors accept bigint or canonical base-10 text and reject JavaScript `number`, including safe integers. |
| `D-CAS-024` | accepted | Rational normal form has coprime numerator/denominator, positive denominator, and unique zero `0/1`; ordinary power uses nonnegative bigint exponents. |
| `D-CAS-025` | accepted | Immutable operational commutative-ring/field dictionaries supply later algorithms but are runtime capabilities, not formal doctrine evidence. |
| `D-CAS-026` | accepted | Polynomial normal form is an immutable descending sparse term list; equal monomials are merged, zero coefficients are removed, and exponents are nonnegative bigint. |
| `D-CAS-027` | accepted | Polynomial parent identity contains coefficient-parent identity, ordered variable list, and selected lex/grlex/grevlex order; no implicit cross-parent arithmetic is performed. |
| `D-CAS-028` | accepted | Initial substitution remains within one polynomial ring; general coefficient/ring maps are a later explicit operation rather than an inferred coercion. |
| `D-CAS-029` | accepted | Initial multivariate division is divisor-order-sensitive, requires an operational field, rejects zero divisors, retains all quotients and the remainder, and enforces a step ceiling. |
| `D-CAS-030` | accepted | The native reference engine registers one or more algorithms under an exact operation/input/output schema contract; available algorithms are deterministically ordered and explicit selection is honored. |
| `D-CAS-031` | accepted | Reference-engine v1 enforces cancellation before an operation, per-operation declared fuel cost, start/end progress, and selected output limits; polling inside heavyweight algorithms is introduced with those algorithms. |
| `D-CAS-032` | accepted | Exact operation descriptors are global, while polynomial operation bundles are ring-specific and include the structural polynomial parent in every operation and schema identity. |
| `D-CAS-033` | accepted | An ideal retains its ordered normalized generator family, including zero entries; Groebner transformations are rows relative to that exact family. |
| `D-CAS-034` | accepted | Buchberger v1 uses a deterministic pair queue, monic new basis elements, no optimization criterion, and explicit pair/basis/reduction/cancellation bounds; faster algorithms remain alternative implementations. |
| `D-CAS-035` | accepted | Ideal membership always returns coefficients and a remainder satisfying `f = sum_i a_i*g_i + r`; `member` is exactly whether the remainder is zero for the supplied Groebner result. |
| `D-CAS-036` | accepted | Groebner and membership schemas validate structural shape and parent agreement but do not silently certify that an externally supplied basis has the Groebner property. |
| `D-CAS-037` | accepted | A unimodular computation retains the complete ideal/basis/membership path and projects coefficients, combination, and remainder; it is not reduced to a Boolean. |
| `D-CAS-038` | accepted | A computational finite basic-open cover is constructed only from a positive unimodular result whose retained combination is exactly one. |
| `D-CAS-039` | accepted | The TypeScript formal commutative-algebra profile is not yet qualified, so the current Zariski result remains computational data and the `CommRingUnimodularPresentation` bridge stays in `CAS-FORMAL-BRIDGE-10`. |
| `D-CAS-040` | accepted | An `m x n` matrix represents `R^n -> R^m` on column vectors; composition is left multiplication and storage is immutable row-major. |
| `D-CAS-041` | accepted | Field row reduction retains `L` with `L*A = rref(A)`, ordered pivot columns, rank, and work count. |
| `D-CAS-042` | accepted | A kernel basis is an `n x k` matrix whose columns generate the nullspace and satisfy `A*K = 0`; `k` is the recorded nullity. |
| `D-CAS-043` | accepted | Module work is split: field-linear presentations can derive from current RREF/kernel matrices, while polynomial-ring modules require a separate module-Groebner/Schreyer layer and must not be approximated by scalar ideal algorithms. |
| `D-CAS-044` | accepted | A field-linear presentation is `R^r -> R^g -> M -> 0` with relation columns; a morphism retains `F*R_source = R_target*W`. |
| `D-CAS-045` | accepted | Quotient coordinates use a left-annihilator projection with an explicit section; field-linear kernels are lifted from the induced quotient-coordinate matrix. |
| `D-CAS-046` | accepted | A morphism cokernel appends the morphism columns to target relations; polynomial-module kernels/cokernels remain gated on module Groebner machinery. |
| `D-CAS-047` | accepted | Additional categorical operations use immutable primitive/derived methods; planning recursively selects least total declared weight with deterministic method-ID ties and rejects cycles/unavailable prerequisites. |
| `D-CAS-048` | accepted | Ring-as-category is a strict one-object runtime category whose endomorphisms are coefficient elements, identity is one, and composition is multiplication. |
| `D-CAS-049` | accepted | Presented-field-module kernels and cokernels are primitive whole operations; kernel-object and cokernel-object are derived registry methods depending on those whole owners. |
| `D-CAS-050` | accepted | Doctrine descriptors are operational metadata with inherited required roles and involutive dual mappings; they do not constitute LF evidence. |
| `D-CAS-051` | accepted | Doctrine qualification succeeds only when every inherited role is explicitly bound to a plannable category operation; missing roles are retained rather than inferred from category names. |
| `D-CAS-052` | accepted | Constructor descriptors retain source/output doctrines, representation layers, introduced roles, dual constructor identity, and compiler-facing lowering rules. |
| `D-CAS-053` | accepted | Generic Freyd adds the operational cokernel role but remains in the additive doctrine; stronger pre-Abelian/Abelian claims require additional capabilities or a concrete qualified reinterpretation. |
| `D-CAS-054` | accepted | Opposite categories execute reversed source/target and composition while opposite descriptors route through doctrine duality; Freyd and CoFreyd are explicit dual constructors. |
| `D-CAS-055` | accepted | Reinterpretation retains public/model conversion functions and lowering rules as compiler input; roundtrip equality is consumer-tested rather than silently assumed by the descriptor. |
| `D-CAS-056` | accepted | Categorical programs retain scoped input/node/output IR and never recover semantics from arbitrary TypeScript function ASTs. |
| `D-CAS-057` | accepted | Compiler v1 resolves and records the selected category method, but lowers the whole operation only through an explicit input/output-schema-preserving algebra binding. |
| `D-CAS-058` | accepted | Tower lowering rules are retained in compilation artifacts; callback inlining, box/unbox cancellation, fusion, routing, and optimization remain later explicit passes. |
| `D-CAS-059` | accepted | Native field-module kernel and cokernel algebra operations reuse the exact input/output schemas of the categorical whole-construction owners, making compiler bindings explicit and schema-preserving rather than coercive. |
| `D-CAS-060` | accepted | `PresentedModule` is the efficient public and executable reinterpretation of `Freyd(AdditiveClosure(RingCategory(F)))`; the tower remains explicit modeling/compiler metadata and does not impose runtime wrapper boxes. |
| `D-CAS-061` | accepted | Reinterpretations are optional explicit compiler inputs whose rules are retained with constructor rules; compiler v1 rejects foreign public categories and duplicate rule identities but does not yet execute representation rewrites or optimization passes. |
| `D-CAS-062` | accepted | The first Freyd acceptance boundary is structural computational agreement of the complete kernel/cokernel results with direct module algorithms; no proof certificate is required, and the generic Freyd tower remains additive rather than being mislabeled Abelian. |
| `D-CAS-063` | accepted | Presented-field-module morphism equality and zero testing use induced matrices on canonical quotient coordinates; raw matrices and relation witnesses remain representation data and do not define categorical congruence. |
| `D-CAS-064` | accepted | Full-column-rank left inverses and full-row-rank right inverses provide the reference linear-algebra substrate for lift-along-monomorphism and colift-along-epimorphism; candidate factorizations are checked again in quotient coordinates. |
| `D-CAS-065` | accepted | Whole module kernels and cokernels retain their input morphisms as well as structural maps, enabling kernel lifts and cokernel colifts without reconstructing or separately pairing universal-construction data. |
| `D-CAS-066` | accepted | The first chain-complex profile is finite, bounded, consecutively integer-graded, and uses `d_n: C_n -> C_(n-1)`; endpoint zero maps are generated internally and every chain law is checked on quotient coordinates. |
| `D-CAS-067` | accepted | First homology is the whole construction `coker(incoming -> ker(outgoing))` and requires `outgoing * incoming = 0`; CAP's broader homology object for an arbitrary composable pair is not silently claimed by this chain-complex tranche. |
| `D-CAS-068` | accepted | First chain maps require one common bounded degree range, retain every component, and validate each differential square using quotient-aware morphism equality; identity and composition are componentwise and revalidated. |
| `D-CAS-069` | accepted | Functorial homology first restricts the selected chain-map component to the target cycle kernel and then descends through the source boundary cokernel; the whole result retains both homology constructions, the cycle map, and the final morphism. |
| `D-CAS-070` | accepted | A deterministic lift through an epimorphism is exposed only for presented modules over the current field-linear category, where RREF supplies a right inverse; recomposition is checked on quotient coordinates and no corresponding claim is made for arbitrary module categories. |
| `D-CAS-071` | accepted | A short exact sequence of bounded complexes consists of two already-validated chain maps plus computed degreewise exactness data: the projection kernel, inverse identifications with the included subobject, and a projection section. No independent hand-written commuting-square witness is stored. |
| `D-CAS-072` | accepted | The connecting map `H_n(C) -> H_(n-1)(A)` retains the quotient-cycle lift, middle boundary, lift into the projection kernel, transport through the retained kernel/subobject identification, target-cycle lift, and final boundary descent. |
| `D-CAS-073` | accepted | Initial generalized morphisms use CAP's span shape `A <- D -> B` with a monic source aid; three-arrow, cospan, pseudo-inverse, common-restriction, and Serre-quotient semantics remain explicit later work rather than aliases for this subset. |
| `D-CAS-074` | accepted | Span composition uses a whole field-module pullback retaining both projections, the comparison matrix, its kernel basis, and a universal lift; composition retains the pullback artifact instead of erasing directly to a resulting span. |
| `D-CAS-075` | accepted | Honest module maps embed as identity-source spans. An honest representative is returned only when the source aid has full domain; partial spans remain partial and are not extended by an arbitrary complement. |
| `D-CAS-076` | accepted | Field resolutions expose both a presentation-derived free complex retaining relation syzygies and a minimal split length-zero resolution; they answer different computational questions and neither is hidden behind the other. |
| `D-CAS-077` | accepted | The presentation resolution retains free terms in degrees zero through two, including zero-rank terms, and reports projective length from the last nonzero term; polynomial-module and Schreyer resolutions remain exclusively in `CAS-MODULE-4B2`. |
| `D-CAS-078` | accepted | Whole homology, functorial homology, connecting morphisms, presentation/split resolutions, and generalized-span composition have field-specific native operation descriptors and runtime schemas, so they execute directly or as `AlgebraComputationGraph` nodes. |
| `D-CAS-079` | accepted | Native graph exposure completes the first homological row without pretending that compiler v1 already expands a generic categorical homology derivation into primitive kernels, lifts, and cokernels; derivation inlining remains a later compiler pass. |
| `D-CAS-080` | accepted | After the complete field-linear homological row, the next selected row is polynomial modules and Schreyer syzygies (`CAS-MODULE-4B2`), which unlock non-field resolutions; constructible geometry remains independently dependency-ready rather than blocked. |
| `D-CAS-081` | accepted | Polynomial free modules expose position-over-term and term-over-position orders with lower basis indices first; the selected module order is part of the structural parent identity rather than ambient mutable state. |
| `D-CAS-082` | accepted | A module leading term divides another only when both polynomial monomial divisibility and basis position agree; module reduction and Buchberger pairing therefore do not decompose into unrelated scalar ideal computations. |
| `D-CAS-083` | accepted | Module Buchberger retains a polynomial transformation row for every basis vector, and membership returns original-generator coefficients plus a module remainder satisfying exact reconstruction. |
| `D-CAS-084` | accepted | A Schreyer free-module parent retains the target module and the leading term of every reference basis vector; induced comparison descends recursively to the target order and then uses the recorded basis-index tie break. |
| `D-CAS-085` | accepted | Schreyer generators are coefficient rows of module S-pairs that reduce to zero against the complete computed module Gröbner basis; each row is recombined with that basis and required to produce the zero module vector. |
| `D-CAS-086` | accepted | A presented polynomial module retains its original relation submodule and its computed module Gröbner basis; quotient normal form is the position-aware module-division remainder, with coefficients and reconstruction data retained. |
| `D-CAS-087` | accepted | A bounded Schreyer resolution recursively uses each current Gröbner basis as differential columns, computes its verified Schreyer syzygies, Gröbner-normalizes the next syzygy submodule, checks consecutive composites, and distinguishes completion from explicit truncation. |

## `CAS-MODULE-4B2C` Result

Presented polynomial modules, free-module maps, and bounded recursive Schreyer
resolutions are implemented in
`src/v3_2/algebra_polynomial_presentation.ts`. A module presentation retains
the original relation family and its module Gröbner basis. Quotient reduction
returns the existing membership result: original-relation coefficients, basis
quotients, and the canonical module remainder.

A free-module map is represented by the images of its ordered source basis;
application, identity, composition, and zero testing are computational. The
resolution algorithm repeatedly installs the current Gröbner basis as a
differential, computes verified Schreyer syzygies, normalizes their submodule,
and continues until no syzygies remain or the caller's length bound is met.
Every consecutive composite is required to be zero.

For the running presentation, the complete resolution has free ranks
`2 <- 3 <- 1` and length two. A length-one request is retained as incomplete,
while a quotient with no relations terminates at length zero without fake
zero stages. Three presentation tests plus the affected module and ideal
suites give 19 passing tests, followed by workspace check, affected lint,
root typecheck, and diff hygiene. No repository-wide aggregate was run.

Semantic checkpoint: `499aea5` (`cas: add polynomial module Schreyer resolutions`).

## `CAS-MODULE-4B2B` Result

Induced Schreyer orders and first syzygy generators are implemented in
`src/v3_2/algebra_polynomial_module.ts`. A Schreyer parent records its target
free module and the complete leading-term family of a module Gröbner basis.
To compare `x^a e_i` and `x^b e_j`, it compares
`x^a LT(g_i)` and `x^b LT(g_j)` in the retained target-module order, then
breaks an exact tie by lower basis index. Because the target may itself use a
Schreyer order, this representation supports later recursive stages.

For every basis pair with one leading position, the syzygy algorithm forms the
module S-pair with unit transformation rows, divides it by the complete basis,
requires zero remainder, subtracts the reduction quotients, and returns the
resulting coefficient vector in the induced Schreyer module. It independently
recombines every output vector with the basis and requires zero.

The running rank-two example yields `(y,-x,-1)` for the relation among
`(x,y)`, `(y,0)`, and `(0,y^2)`. Tests also run module Buchberger recursively
on the syzygy module and reject a deliberately truncated non-Gröbner input.
Five focused module tests plus the affected polynomial and ideal suites give
29 passing tests, followed by workspace check, affected lint, root typecheck,
and diff hygiene. No repository-wide aggregate was run.

Semantic checkpoint: `96dad7f` (`cas: add Schreyer module syzygies`).

## `CAS-MODULE-4B2A` Result

The polynomial free-module substrate and reference Buchberger engine are
implemented in `src/v3_2/algebra_polynomial_module.ts`. A structural parent
records the polynomial ring, free rank, and either position-over-term or
term-over-position order. Vectors are canonical arrays of sparse polynomials,
while leading terms are selected globally using the module order and an
explicit lower-position-first tie break.

Module division requires equal basis position in addition to scalar monomial
divisibility. The deterministic Buchberger algorithm queues S-pairs only for
basis elements with matching leading position, normalizes new basis vectors,
retains transformations to the original generator family, enforces pair,
basis, per-reduction, total-reduction, and cancellation limits, and reports
progress. Membership retains basis quotients, coefficients in the original
generators, and a remainder.

The distinguishing test starts from `(x,y)` and `(y,0)` in a rank-two module
with position-over-term order. Their S-pair creates `(0,y^2)`, demonstrating
that the implementation is a module computation rather than two scalar ideal
computations. Four focused tests cover POT/TOP leading-term differences,
position-aware division and reconstruction, basis transformations, positive
and negative membership, schemas, foreign modules, non-fields, zero divisors,
limits, and cancellation. Together with the affected polynomial and ideal
suites, 28 tests pass, followed by workspace check, affected lint, root
typecheck, and diff hygiene. No repository-wide aggregate was run.

Semantic checkpoint: `ecf1b97` (`cas: add polynomial module Buchberger engine`).

## `CAS-HOMOLOGICAL-7A6` Result And Row Completion

Native graph operations are implemented in
`src/v3_2/algebra_homological_reference_operations.ts`. The field-specific
bundle revalidates bounded complexes, chain maps, short exact sequences, and
generalized spans at operation boundaries. It exposes whole operations for:

- homology in one degree;
- the map on homology induced by a chain map;
- a connecting morphism;
- presentation-derived and split resolutions; and
- generalized-span composition.

All implementations run inside the native TypeScript reference engine and
retain their complete structured results. Tests execute homology and a
presentation resolution as computation-graph nodes, and exercise functorial
homology, connecting morphisms, a split resolution, and generalized-span
composition through the same operation/engine contracts.

Three native-operation tests plus the affected homological, generalized-span,
resolution, graph, reference-engine, and module suites give 46 passing tests,
followed by workspace check, affected lint, root typecheck, and diff hygiene.
No repository-wide aggregate was run.

Semantic checkpoint: `ab68a11` (`cas: expose native homological graph operations`).

This completes `CAS-HOMOLOGICAL-7A` at its stated initial boundary. The row
does not claim unbounded complexes, three-arrow/cospan/Serre-quotient
generalized morphisms, arbitrary-ring resolutions, or compiler expansion of
generic categorical derivations. Polynomial-module and Schreyer resolutions
belong to `CAS-MODULE-4B2`; broader generalized-morphism and compiler passes
require later concrete consumers.

## `CAS-HOMOLOGICAL-7A5` Result

Field-linear free resolutions are implemented in
`src/v3_2/algebra_resolution.ts`. The presentation-derived resolution of
`M = coker(R: F^r -> F^g)` is the augmented bounded complex

```text
0 -> ker(R) -> F^r -> F^g -> M -> 0.
```

It retains the relation morphism, its whole syzygy kernel, the augmentation,
all three homology computations, and a shortened projective length from zero
through two. Exactness is checked by the augmentation equation, recovery of
`M` as degree-zero homology, and vanishing higher homology.

The split resolution separately uses the canonical quotient realization to
construct inverse maps between `M` and `F^dim(M)`. This is the genuinely
minimal length-zero resolution available in the present field-linear category,
not a claim about modules over general rings.

Three resolution tests cover redundant relations with a first syzygy,
independent relations, a free module, projective-length shortening, and the
split augmentation/inverse equations. Together with the affected homological,
generalized-span, module, and matrix suites, 32 tests pass, followed by
workspace check, affected lint, root typecheck, and diff hygiene. No
repository-wide aggregate was run.

Semantic checkpoint: `052032a` (`cas: add field module resolutions`).

## `CAS-HOMOLOGICAL-7A4` Result

The initial generalized-morphism layer is implemented in
`src/v3_2/algebra_generalized.ts`. It follows CAP's span representation:

```text
A <-sourceAid- D -arrow-> B
```

where the source aid is computationally checked to be monic. The layer also
implements a whole pullback of presented field-module maps and its universal
lift. Pullbacks are computed on quotient coordinates as kernels of
`[left, -right]`, then projected back to the presented modules through their
retained quotient realizations.

Composition forms the pullback of the first span's arrow and the second
span's source aid. The whole composition retains both input spans, the
pullback, and the resulting span. Honest morphisms embed with identity source
aid, and compositions of honest spans recover direct composition. A partial
domain remains partial under composition; requesting an honest representative
requires the source aid to be onto as well as monic.

Three generalized-span tests cover the pullback square and universal lift,
honest embedding/composition/identity, partial-domain composition, and
rejection of invalid source aids, noncomposable spans, invalid cones, and
honest representatives for partial maps. Together with the affected module
and matrix suites, 22 tests pass, followed by workspace check, affected lint,
root typecheck, and diff hygiene. No repository-wide aggregate was run.

Semantic checkpoint: `3961bc5` (`cas: add generalized module spans`).

## `CAS-HOMOLOGICAL-7A3` Result

Degreewise short exact sequences and connecting morphisms are implemented in
`src/v3_2/algebra_homological.ts`, supported by the field-specific epimorphism
lift in `src/v3_2/algebra_module.ts`. The short-exact constructor consumes two
validated chain maps `A -> B -> C`. In each degree it checks the zero
composite, computes `ker(B -> C)`, constructs inverse quotient-aware maps
between that kernel and `A`, and computes a section of the degreewise
projection. A failed monomorphism, epimorphism, or kernel identification is
reported as failed exactness rather than retained as an assertion.

The connecting computation lifts quotient cycles to the middle complex,
applies the middle differential, lifts the boundary into the retained kernel
of the preceding projection, transports it to the subcomplex, lifts it into
subcomplex cycles, and descends through quotient boundaries. Every
intermediate map is retained in the whole result. The focused example

```text
0 -> (0 -> F) -> (F -id-> F) -> (F -> 0) -> 0
```

computes the identity `H_1(F -> 0) -> H_0(0 -> F)`, and tests check all four
factorization stages. A degreewise sequence with the wrong included image and
an out-of-range connecting degree are rejected.

Seven focused homological tests and the affected matrix, module, category,
and Freyd suites give 33 passing tests, followed by workspace check, affected
lint, root typecheck, and diff hygiene. No repository-wide aggregate was run.

Semantic checkpoint: `5f22b08` (`cas: add homology connecting morphisms`).

## `CAS-HOMOLOGICAL-7A2` Result

Bounded chain maps and functorial homology are implemented in
`src/v3_2/algebra_homological.ts`. A chain map retains one component in every
degree of a common finite bound and validates
`d_target * f_n = f_(n-1) * d_source` on quotient coordinates. Identity and
composition are constructed componentwise and passed back through the same
validation boundary.

The induced homology computation is retained as a whole factorization. It
first lifts `f_n` restricted to source cycles into the target cycle kernel,
then composes with the target homology projection and colifts through the
source boundary cokernel. Tests inspect both factorization equations, not only
the final matrix. Scalar chain maps induce the expected scalar on homology;
identity and composition agree with the corresponding computed homology maps,
and a noncommuting differential square is rejected.

Five focused homological tests and the affected matrix, module, category, and
Freyd suites give 31 passing tests, followed by workspace check, affected
lint, root typecheck, and diff hygiene. No repository-wide aggregate was run.

Semantic checkpoint: `8b97bad` (`cas: add functorial module homology`).

## `CAS-HOMOLOGICAL-7A1` Result

The first homological substrate is implemented across
`src/v3_2/algebra_matrix.ts`, `src/v3_2/algebra_module.ts`, and
`src/v3_2/algebra_homological.ts`. Exact RREF-derived left and right inverses
support quotient-aware lifts and colifts. Presented-module morphisms now have
an explicit induced matrix on canonical quotient coordinates; categorical
equality, zero testing, factorization checks, and chain laws use that induced
map rather than raw representatives or relation witnesses.

Whole kernels and cokernels retain their input morphisms and support kernel
lifts and cokernel colifts. The bounded chain-complex constructor validates
consecutive integer degrees, exact source/target endpoints, and every
`d_(n-1) * d_n = 0` law. Homology retains its incoming and outgoing maps,
cycle kernel, boundary lift, quotient cokernel, and resulting object. At the
two bounded endpoints, canonical zero maps supply the missing incoming or
outgoing differential.

Three focused homological tests cover a nontrivial three-term complex,
homology in every degree, the complete boundary-factorization construction,
and malformed bounds/endpoints/chain laws. The affected matrix, module,
category, and Freyd suites cover one-sided inverses, quotient representatives,
zero maps, lifts/colifts, and regression of compiled whole constructions. The
29-test focused set passes, followed by workspace check, affected lint, root
typecheck, and diff hygiene. No repository-wide aggregate was run.

Semantic checkpoint: `66ed5a8` (`cas: add quotient-aware module homology`).

Remaining `CAS-HOMOLOGICAL-7A` work is deliberately separate: chain maps and
functorial maps on homology, connecting morphisms for short exact sequences,
an initial generalized-morphism representation, and bounded resolution
algorithms. Polynomial-module/Schreyer resolutions remain gated in
`CAS-MODULE-4B2` rather than being approximated by field-only code.

## `CAS-FREYD-6B` Result

The first concrete CAP-style reinterpretation is implemented in
`src/v3_2/algebra_freyd.ts`, with native whole module operations in
`src/v3_2/algebra_module_reference_operations.ts`. For a field `F`, the model
retains the `AdditiveClosure` then `Freyd` constructor tower and its matrix and
presentation lowering rules, while exposing direct presentation matrices as
the public and executable representation. The runtime therefore avoids
constructing wrapper objects for the modeling tower.

Whole categorical kernel and cokernel nodes bind to schema-identical native
algebra operations and compile into `AlgebraComputationGraph`. The compilation
artifact records the selected primitive categorical methods, both constructor
rules, and the direct-presentation reinterpretation rule. Reinterpretation
rules are retained metadata in this profile; callback inlining, representation
rewrite execution, fusion, and optimization remain later explicit passes.

Three focused Freyd tests cover tower/reinterpretation packaging, compiled
kernel and cokernel execution, structural agreement of every retained whole
result with direct `algebraModuleKernel` and `algebraModuleCokernel`
computations, schema-preserving bindings, and rejection of missing bindings,
duplicate compiler rules, and foreign reinterpretations. Together with the
affected compiler, tower, category, module, graph, and reference-engine suites,
43 tests pass, followed by workspace check, affected lint, root typecheck, and
diff hygiene. No repository-wide aggregate was run.

Semantic checkpoint: `2f26a59` (`cas: compile Freyd module constructions`).

## `CAS-COMPILER-6A` Result

The first staged compiler is implemented in
`src/v3_2/algebra_categorical_program.ts`. It provides a scoped retained
categorical-program builder, typed category-operation nodes, named outputs,
method-resolution traces, explicit category-to-algebra operation bindings,
tower-rule retention, lowering into `AlgebraComputationGraph`, and execution
through the native engine. Three compiler tests cover an executable retained
double-negation program, module-tower rule retention, and missing/duplicate/
foreign lowering failures. Together with the affected tower, category, graph,
and engine suites, 33 tests pass, followed by workspace check, affected lint,
root typecheck, and diff hygiene.

Semantic checkpoint: `c28da8f` (`cas: add staged categorical program lowering`).

## `CAS-TOWER-5C` Result

Constructor towers are implemented in `src/v3_2/algebra_tower.ts`. The layer
provides validated constructor descriptors, doctrine-compatible tower
composition, introduced-role and lowering-rule aggregation, AdditiveClosure,
Freyd and CoFreyd metadata, doctrine-indexed opposite descriptors, executable
opposite categories, and explicit computational reinterpretations. The
module tower remains correctly additive plus an introduced cokernel role,
avoiding a generic Abelian overclaim. Five tower tests and the fifteen affected
doctrine/category/module tests pass, followed by workspace check, affected
lint, root typecheck, and diff hygiene.

Semantic checkpoint: `dd910b0` (`cas: add categorical tower descriptors`).

## `CAS-DOCTRINE-5B` Result

Operational doctrine metadata is implemented in `src/v3_2/algebra_doctrine.ts`.
It provides validated acyclic hierarchies, involutive doctrine and role
duality, inherited capability-role closure, explicit role bindings, and
qualified/missing reports based on actual operation planning. The base
registry contains Category, Preadditive, Additive, Pre-Abelian, and Abelian
descriptors. Four focused doctrine tests cover hierarchy/duality, honest
missing-role reporting for the module category, complete qualification, and
cycle/non-involutive rejection; the four affected category tests also pass,
followed by workspace check, affected lint, root typecheck, and diff hygiene.

Semantic checkpoint: `02ac3d0` (`cas: add operational category doctrines`).

## `CAS-CATEGORY-5A` In-Progress Result

The first category-runtime subtranche is implemented in
`src/v3_2/algebra_category.ts`. It provides strict category identity and
composition hooks, typed operation schemas, immutable primitive/derived
methods, weighted recursive planning with retained prerequisite trees, and
normalized execution. Two focused tests cover cheaper derived selection,
nested calls, unavailability, duplicate methods, and derivation cycles.
Ring-as-category and field-module category instances remain required before
this ledger row is complete.

Core-registry checkpoint: `90cfca0` (`cas: add computable category registry`).

The completed consumer layer is implemented in
`src/v3_2/algebra_category_instances.ts`. Four category tests cover weighted
planning, cycle/unavailable/duplicate rejection, strict ring-category
identity/composition, module-category identity/composition, whole
kernel/cokernel execution, and derived object projections. Together with the
seven module and nine matrix tests, the affected 20-test set passes, followed
by workspace check, affected-file lint, root typecheck, and diff hygiene.

Consumer checkpoint: `64b4c7c` (`cas: add ring and module category instances`).

## `CAS-MODULE-4B1` Result

The field-linear presentation layer is implemented in
`src/v3_2/algebra_module.ts`. It provides free and finitely presented modules,
relation-witnessed morphisms, identities and composition, explicit quotient
projection/section realizations, free kernel objects with inclusions,
presented cokernels with projections, and matrix syzygies. The quotient model
checks `Q*R = 0` and `Q*S = id`; kernel inclusions satisfy the induced zero
equation. Seven focused module tests and the nine affected matrix tests pass,
followed by workspace check, affected-file lint, root typecheck, and diff
hygiene. Polynomial-module term orders, module Groebner bases, Schreyer
syzygies, and resolutions remain exclusively in `CAS-MODULE-4B2`.

Semantic checkpoint: `707a7da` (`cas: add field-linear module presentations`).

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

## `CAS-EXACT-2A` Result

The exact foundation is implemented in `src/v3_2/algebra_parent.ts` and
`src/v3_2/algebra_exact.ts`. It remains contributor-only and provides:

Semantic checkpoint: `36dc108` (`cas: add exact integer and rational domains`).

- stable parent identities and parent-checked elements;
- canonical integer and rational parents;
- bigint-only integer payloads;
- rational payloads reduced to coprime numerator and positive denominator;
- canonical base-10 integer and `n/d` acquisition;
- integer ring arithmetic, comparison, gcd, exponentiation, and Euclidean
  quotient/remainder for every divisor sign;
- rational field arithmetic, comparison, inversion, division, and powers;
- canonical text and newline-terminated JSON that represents bigint as text;
- runtime schemas rejecting JavaScript numbers and foreign parents;
- topology-only graph flow for exact inputs; and
- immutable operational integer-ring and rational-field dictionaries for
  coefficient-polymorphic algorithms.

Focused evidence in `tests/v3_2_algebra_exact_tests.ts` covers twelve positive
and negative exact-domain cases. All 33 engine/graph/exact focused tests pass
together, followed by affected-file lint, root typecheck, and diff hygiene.

## `CAS-POLY-2B` Result

The first sparse polynomial layer is implemented in
`src/v3_2/algebra_polynomial.ts`. It is generic over the operational
commutative-ring domain and provides:

Semantic checkpoint: `7b6b929` (`cas: add sparse polynomial algebra`).

- structural polynomial-ring parents over ordered variable lists;
- lexicographic, graded lexicographic, and graded reverse lexicographic
  monomial comparison;
- nonnegative bigint exponent vectors;
- canonical merging, zero removal, and descending sparse ordering;
- zero, one, constants, variables, and monomial construction;
- addition, negation, subtraction, multiplication, and nonnegative powers;
- equality and leading-term observation;
- stable text and newline-terminated JSON without bigint ambiguity;
- ring-specific runtime schemas;
- same-ring polynomial substitution; and
- ordered multivariate division over operational fields with quotients,
  remainder, step count, zero-divisor rejection, and explicit limits.

Focused evidence in `tests/v3_2_algebra_polynomial_tests.ts` covers thirteen
positive and negative polynomial cases, including coefficient-generic integer
arithmetic, rational division reconstruction, order distinctions, structural
ring separation, schema rejection, and zero-variable rings. All 46 focused
CAS tests pass together, followed by workspace check, affected-file lint,
root typecheck, and diff hygiene.

## `CAS-MATRIX-4A` Result

The first exact matrix layer is implemented in `src/v3_2/algebra_matrix.ts`
and `src/v3_2/algebra_matrix_reference_operations.ts`. It provides:

Semantic checkpoint: `442cbff` (`cas: add exact matrices and kernel bases`).

- structural matrix-space parents over operational coefficient rings;
- immutable row-major values and exact entry access;
- zero and identity matrices, arithmetic, transpose, equality, and standard
  multiplication;
- explicit `m x n` column-vector-map orientation;
- field RREF with retained left row-operation transformation;
- ordered pivot columns, rank, work count, and progress;
- kernel generators as columns of an `n x k` matrix;
- field, dimension, entry, intermediate-storage, fuel, and cancellation gates;
- runtime schemas and deterministic coefficient-text JSON; and
- native negate/add/transpose/RREF/kernel operations with a retained
  double-transpose graph.

Focused evidence in `tests/v3_2_algebra_matrix_tests.ts` covers nine positive
and negative matrix cases, including empty dimensions, composition,
`L*A = rref(A)`, `A*K = 0`, non-field rejection, limits, schemas,
serialization, native operations, and graph composition. All 85 focused CAS
tests pass together, followed by workspace check, affected-file lint, root
typecheck, and diff hygiene.

## `CAS-ENGINE-2C` Result

The native execution layer is implemented in
`src/v3_2/algebra_reference_engine.ts` and
`src/v3_2/algebra_reference_operations.ts`. It provides:

Semantic checkpoint: `765aa32` (`cas: add native TypeScript reference engine`).

- immutable typed reference-implementation declarations;
- multiple algorithms per exact operation contract;
- duplicate and schema-contract collision rejection;
- deterministic algorithm ordering and explicit selection;
- an in-process engine with no I/O or external CAS dependency;
- per-operation fuel costs and pre-execution cancellation;
- deterministic start/completion progress events;
- structured result metadata flowing through the general engine validator;
- global selected integer/rational operations;
- ring-specific polynomial negate/add/multiply/power/division bundles;
- polynomial term-output ceilings and division step budgets; and
- direct and retained multi-node graph execution.

Focused evidence in `tests/v3_2_algebra_reference_engine_tests.ts` covers ten
positive and negative native-engine cases. All 56 focused CAS tests pass
together, followed by workspace check, affected-file lint, root typecheck,
and diff hygiene.

## `CAS-ZARISKI-3B` Result

The first geometry-facing computation is implemented in
`src/v3_2/algebra_zariski.ts` and
`src/v3_2/algebra_zariski_reference_operations.ts`. It provides:

Semantic checkpoint: `ebbe15f` (`cas: add computational Zariski covers`).

- a whole unimodular-combination result retaining the ideal, reduced basis,
  membership computation, coefficients, combination, and remainder;
- direct finite generator-family acquisition;
- a positive-only computational Zariski-cover presentation;
- structural validators that reject projection drift;
- deterministic serialization of generators, coefficients, combination, and
  remainder;
- native unimodular and cover operations; and
- a retained `ideal -> unimodular result -> cover presentation` graph.

Focused evidence in `tests/v3_2_algebra_zariski_tests.ts` covers nine positive
and negative cases: `x,1-x`, non-unimodular and empty families, whole-schema
drift, serialization, native execution, graph composition, limits,
cancellation, and the explicit absence of a formal adapter. All 76 focused
CAS tests pass together, followed by workspace check, affected-file lint,
root typecheck, and diff hygiene.

## `CAS-IDEAL-3A` Result

The first ideal layer is implemented in `src/v3_2/algebra_ideal.ts` and
`src/v3_2/algebra_ideal_reference_operations.ts`. It provides:

Semantic checkpoint: `58f51f2` (`cas: add polynomial ideals and Buchberger`).

- ordered parent-checked polynomial ideals;
- a deterministic transparent Buchberger reference algorithm;
- monic initial and newly discovered basis elements;
- retained transformation rows expressing each basis element in the original
  generators;
- cancellation polling between S-pairs;
- pair, basis-size, per-division, and total-reduction ceilings;
- S-polynomial construction and Buchberger-pair inspection;
- a reduced-basis postpass retaining transformation rows;
- ideal linear-combination evaluation;
- membership coefficients, basis quotients, canonical remainder, and exact
  reconstruction data for both positive and negative outcomes;
- immutable structural schemas and deterministic text-oriented JSON; and
- ring-specific native Groebner/reduced-basis/membership operations, including
  a retained `ideal -> basis -> reduced basis` graph pipeline.

Focused evidence in `tests/v3_2_algebra_ideal_tests.ts` covers eleven positive
and negative ideal cases, including every transformation reconstruction,
every resulting S-pair, positive/nonmember decompositions, the zero ideal,
limits, cancellation, non-field rejection, schema drift, serialization,
native execution, and graph composition. All 67 focused CAS tests pass
together, followed by workspace check, affected-file lint, root typecheck,
and diff hygiene.

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
