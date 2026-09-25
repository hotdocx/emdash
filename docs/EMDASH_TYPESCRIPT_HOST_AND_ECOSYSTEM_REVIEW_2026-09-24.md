# Emdash's TypeScript Host, Package And Ecosystem

Date: 2026-09-24 (America/Toronto)
Status: architectural review and proposed next consumer; no new implementation goal selected
Reviewed checkout: `9de1a48faee8bd217c7c3614dc097bfa536e362d`

This extends the [OSCAR review](EMDASH_OSCAR_AND_ALGEBRA_WORKBENCH_REVIEW_2026-09-24.md)
and the completed [polynomial/internal-reuse plan](TYPESCRIPT_EMDASH_ALGEBRA_WORKBENCH_PLAN.md).
It answers the user's broader question about host-language programmability,
ecosystem access and the existing npm distribution. It preserves the
[computation-first CAS architecture](TYPESCRIPT_EMDASH_FOCUSED_CAS_AND_CATEGORICAL_ENGINE_PLAN.md)
and the [current qualification boundaries](TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md).

## Assessment

**TypeScript is Emdash's host programming language; explicit Core is its
internal mathematical/proof language.** Direct TypeScript authoring already
lets users employ ordinary functions, modules, data structures and application
libraries around Emdash computations and declarations. This is an intentional
embedding, not merely an incidental choice of compiler implementation language.
The general-purpose programming aspect in the user's Lean comparison is
therefore already supplied by the architecture.

The OSCAR comparison has three useful, separate dimensions:

| Dimension | Current assessment |
| --- | --- |
| Host programming and ecosystem access | Available by design, with real npm distribution and existing application-library consumers |
| Interoperability between mathematical engines and constructions | Demonstrated for selected operations; richer representations and engine combinations need their own contracts and consumers |
| Formal realization and assurance | Typed data, explicit assumed declarations and selected checked-proof routes exist; automatic certification is an optional capability |

The recent probes mainly strengthened the second and third rows. A broader
ecosystem consumer is now more informative than another certification probe.
There is a concrete engineering route to comparable integration functionality,
and no identified language-level obstacle to using TypeScript libraries around
the supported mathematical objects. This is not evidence of complete OSCAR
algorithm coverage, equivalent performance, or every foreign-engine integration
mechanism. Those remain distinct empirical questions.

## What the Julia/OSCAR analogy contributes

OSCAR's parent model separates a Julia element type from the particular ring,
field or other mathematical structure to which the value belongs. Its GAP
integration uses explicit maps for supported domains and elements. Emdash's
runtime parents and realization maps serve corresponding responsibilities.
[OSCAR parents](https://docs.oscar-system.org/v1/General/faq/),
[GAP integration](https://docs.oscar-system.org/v1/DeveloperDocumentation/gap_integration/).

Host-language access alone does not choose a mathematical visualization.
Makie's recipes, for example, explicitly map custom objects into supported
plot inputs or define new plotting functions. The corresponding Emdash design
is a small mathematical adapter into ordinary plotting data: select the
embedding, coordinates, projection and approximation, then let the library
render. [Makie recipes](https://docs.makie.org/stable/explanations/recipes).

For the existing polynomials over Q, the real-locus view selects Q-to-real
interpretation and bounded floating-point sampling. A group action, chain
complex or polyhedral object would have a different view contract. Display
data must retain its source identity and interpretation without replacing the
exact mathematical objects. An interactive selection can propose a new input
or construction; its geometric appearance does not establish an equation.

Julia also supplies native multiple dispatch. TypeScript can expose explicit
operations, adapters and capability selection through ordinary APIs, but its
static types do not create Julia's runtime dispatch semantics. Reuse the
existing [operation/engine contracts](../src/v3_2/algebra_engine.ts) when such
selection is needed. Simple host functions need no computation graph merely
to be useful. [Julia methods](https://docs.julialang.org/en/v1/manual/methods/).

## What the Lean comparison contributes

Lean supports ordinary compiled programming and C-ABI interoperability within
its own language/toolchain. Its compiler and kernel still have different
roles: compiled `partial` functions can be opaque to logical reasoning, and
`unsafe` functions bypass kernel checking. A common language does not make
every runtime behavior part of trusted conversion.
[Lean elaboration/compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/),
[Lean FFI](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/).

Emdash's corresponding application programming is TypeScript/JavaScript.
Users can compute, build declarations, call libraries and assemble interfaces
without waiting for an Emdash-specific general-purpose runtime. Native access
can use host adapters; Node-API, for example, exposes a C API for native addons.
Browser, native-addon and external-process deployments have different execution
contracts and should remain explicit.
[Node-API](https://nodejs.org/download/release/v24.11.1/docs/api/n-api.html).

The distinction that matters is reasoning about the host program itself.
TypeScript annotations are erased, and arbitrary TypeScript execution is not
an Emdash term or a proof of its result. Proving properties of a host algorithm
would require an explicit model, translation or deliberately supported program
representation. This is separate from using the algorithm to compute useful
data or construct a checked Core term.
[TypeScript type erasure](https://www.typescriptlang.org/docs/handbook/2/basic-types.html#erased-types).

The existing implementations already make this distinction:

- [Categorical authoring](../src/v3_2/categorical_program.ts) lowers its
  construction callbacks immediately to explicit terms. It does not retain
  arbitrary callbacks as mathematical semantics.
- [Categorical CAS programs](../src/v3_2/algebra_categorical_program.ts) retain
  an explicit computation representation and lower selected whole operations
  to algebra graphs. They do not recover semantics from arbitrary TypeScript.
- [Core checking](../src/v3_2/checker.ts) checks the resulting mathematical
  terms under their selected environment and runtime profile.

Continue using TypeScript for ordinary programming and explicit builders/IR
where mathematical inspection, replay or compilation is required. Neither a
new general-purpose language nor a verified TypeScript compiler is a prerequisite
for the ecosystem objective.

## What is already demonstrated

| Evidence | Capability and limit |
| --- | --- |
| Published `@hotdocx/emdash` | External applications can consume supported Core/authoring/workspace APIs as a normal package; the release and checkout expose different API revisions |
| [Existing print pipeline](../emdash2/print/src/pipeline/commonMarkdownPipeline.tsx) and [dependencies](../emdash2/print/package.json) | Real TypeScript/JavaScript ecosystem use, including React, KaTeX, Arrowgram, Mermaid and Vega/Vega-Lite; the pipeline compiles Vega-Lite specs and renders SVG |
| [Polynomial workbench](../src/v3_2/algebra_polynomial_workbench.ts) | Same parent-aware source supports native/Singular computation, numerical sampling and formal interpretation; its HTML/SVG view is custom, so this probe alone does not demonstrate a third-party plotting-library adapter |
| [External module reuse](../src/v3_2/algebra_external_module_reuse.ts) | Actual Singular coefficients survive into typed Core matrices, a constructed whole complex and a further internal matrix action, with one explicit adopted equation |

The last row includes focused Lambdapi observations of the retained column and
action. Its TypeScript signature mirrors remain opaque; it does not newly
qualify standalone TypeScript reduction of the complex projections. Native
exact arithmetic checks the returned relation. Automatic proof reconstruction,
complete kernel generation and homology computation were not acceptance criteria
and were not established by that example.

Thus basic external-result-to-internal-construction integration is demonstrated
for this slice. The missing evidence for the user's ecosystem question is a
convenient **external package consumer of the newer mathematical APIs**, using
an ordinary library on data derived from the same mathematical source.

## The npm package is a central boundary

Public registry metadata and the published tarball were inspected read-only
on 2026-09-24 local time (2026-09-25 UTC). The registry's `latest` endpoint
returned **`@hotdocx/emdash` 0.3.0**. Its exports are `.`, `/authoring`,
`/workspace`, `/benchmark` and `/package.json`, with ESM, CommonJS and TypeScript
declarations. [Registry metadata](https://registry.npmjs.org/@hotdocx%2femdash/latest),
[inspected 0.3.0 artifact](https://registry.npmjs.org/@hotdocx/emdash/-/emdash-0.3.0.tgz).

The private root workbench's name is `emdash`; the distributable package is
the scoped `@hotdocx/emdash`, owned by [its manifest](../packages/emdash/package.json)
and [guide](../packages/emdash/README.md). The four curated source entries
are deliberately narrower than the contributor barrel:
[Core](../src/v3_2/package_core.ts),
[authoring](../src/v3_2/package_authoring.ts),
[workspace](../src/v3_2/package_workspace.ts) and
[benchmark](../src/v3_2/package_benchmark.ts).

Neither those current entries nor the published declaration entries expose the
new algebra/workbench workflows. The published archive contains no algebra-
or polynomial-named modules. Furthermore, the published workspace declaration
entry predates several current workspace exports, including the module-theorem
authoring facade. Matching the checkout's `0.3.0` manifest string is therefore
not evidence that consumers receive the checkout's API surface.

The package gives us an existing distribution and compatibility contract.
The next implementation should curate the smallest additional computational
surface needed by a real consumer, inspect its dependency closure and test an
actual packed artifact. A possible `/algebra` entry is a proposal, not a current
export. Keep browser-safe mathematical operations separate from Node process
adapters. Keep plotting-library dependencies in the consumer or a selected
adapter. Importing a polynomial helper should not require a formal environment
or process transport just because the current repository demo combines them.

Use a local package tarball to qualify new exports before a separately selected
release. Public metadata inspection needs no publishing credential; this review
does not change package contents, version, release status or registry state.

## Recommended next consumer

Test the statement: **an ordinary TypeScript application can import Emdash's
supported mathematical API, compute with a source-owned object, and use a
standard ecosystem library to explore a derived view of that same object.**

Prefer Vega-Lite for the first consumer because the repository already uses
it. Reuse the current bounded polynomial sampler and feed its segments to a
normal visualization specification. Observable Plot is another reasonable
future consumer: its official npm API includes TypeScript declarations and
ordinary application integration. Selecting both adds little to the first
mechanism test. [Observable Plot](https://observablehq.github.io/plot/getting-started).

Proposed acceptance, to be activated in the existing workbench plan if selected:

| Step | Evidence required |
| --- | --- |
| Curate the package surface | One supported mathematical slice; checked public declarations and dependency closure; browser imports do not pull in Node adapters |
| Consume the artifact externally | A clean fixture imports the locally packed package through public exports, without `src/` paths or repository aliases; record exactly which artifact is tested |
| Reuse mathematical data in a library | Exact polynomial objects drive computation and the existing sampler; a real Vega-Lite view consumes derived segments without a second handwritten formula |
| Exercise ordinary application programming | A TypeScript event handler changes the source or viewport and recomputes the view; any asynchronous response remains bound to the correct source revision |
| Preserve useful distinctions | Exact values and approximate views are identifiable; ordinary compute/render works without a proof goal; optional internal realization/adoption retains its existing explicit contract |
| Qualify the bounded consumer | Focused API, artifact and browser checks, including source edits and unsupported numeric interpretations; retain the user's aggregate waiver and record release qualification separately |

Do not turn this into a new notebook, plugin framework or book replacement.
The initial consumer can be a small package example/fixture. If later embedded
in the existing book, follow its current source ownership and print workflow.
This tests the user's intended benefit directly and makes API friction visible.

## Subsequent opportunities

| Priority after that consumer | Design opportunity | Evidence before expansion |
| --- | --- | --- |
| Host execution | Add a worker or external-process adapter when a selected calculation blocks interaction; pass explicit data and source identity | Responsive UI, bounded cancellation/failure and stale-result controls on a measured workload |
| Mathematical exchange | Reuse exact domain encodings and parent contracts across worker/service boundaries; distinguish process handles from portable values | Round-trip and wrong-parent controls for the chosen object family; no universal serialization framework required |
| Authoring ergonomics | Improve typed builders, package examples and diagnostics at the points the consumer exposes | A small mathematical development can be expressed and reused through public APIs without hand-building incidental plumbing |
| Diagrams and executable documents | Derive Arrowgram/Vega views and explanatory tables from retained mathematical objects and existing book sources | One real diagram/document consumer with source-linked regeneration |
| Broader CAS composition | Select richer coefficients or a second external engine, preserving explicit maps and whole-operation interfaces | External data reused across a genuinely new semantic/backend boundary, with measured transport and lifetime behavior |

Node workers are an available host facility for CPU-intensive JavaScript;
asynchronous I/O and CPU parallelism are different concerns. The existing
[algebra graph](../src/v3_2/algebra_graph.ts) is a bounded sequential executor,
so adding a worker for one consumer does not establish a general scheduler.
[Node worker documentation](https://nodejs.org/download/release/v24.11.1/docs/api/worker_threads.html).

Algorithm breadth, interoperability, host ergonomics, performance and formal
assurance should continue to have separate acceptance evidence. A useful
computation or visualization can succeed without proof reconstruction; a
successful chart does not qualify a new mathematical interpretation.

## Integration and review evidence

The user selected local main integration of the completed continuation.
`main` was fast-forwarded cleanly from `dde9f23d` through the planning checkpoint
`f08398bf` to implementation checkpoint `9de1a48f`. All 65 registered worktrees
were clean at the review inventory. There were no temporary uncommitted changes
to discard. The completed persistent goal remains complete; the proposal above
does not silently activate another goal.

This review inspected current source/export owners, the existing plans, the
published npm metadata/declaration entries, and the linked primary documentation.
It did not run a new Lean/OSCAR experiment or a package-consumer executable.
The earlier focused implementation evidence is retained in the workbench plan.
`./scripts/emdash dev docs` passes (90 local links in changed Markdown).
The four documents also pass local-target, fence and whitespace inspection;
the exact staged diff contains only this review and its three routing/status
updates. Full TypeScript and repository-wide aggregates remain waived by the user.
