# Emdash, OSCAR and an Integrated Algebra Workbench

Date: 2026-09-24
Status: architectural review; accepted bounded consumer has a linked execution plan
Reviewed source: `main` at `df061c52`, initially clean

Continuation (2026-09-24): the user accepted this review and the consolidated
handoff, and selected its first bounded polynomial consumer. The
[workbench plan](TYPESCRIPT_EMDASH_ALGEBRA_WORKBENCH_PLAN.md) now owns execution,
current status and validation on a dedicated local branch/worktree. The review
below retains its design-time scope and evidence; implementation is not implied
by these proposals.

The [host/ecosystem follow-up](EMDASH_TYPESCRIPT_HOST_AND_ECOSYSTEM_REVIEW_2026-09-24.md)
reviews the broader Julia/OSCAR and Lean comparisons, verifies the published
`@hotdocx/emdash` boundary, and proposes a package consumer using an ordinary
visualization library. It complements the completed CAS/internal-reuse probes.

## Assessment

The OSCAR analogy is useful. TypeScript can serve as Emdash's common programming,
authoring and application language. Emdash's algebra objects, operation contracts
and adapters would supply the integration layer; selected TypeScript, native,
WASM or external engines would supply algorithms. Explicit Core and Lambdapi add
the formal mathematics and checking boundary. These are different responsibilities.

This clarifies the existing computation-first architecture rather than replacing
it. The [focused CAS plan](TYPESCRIPT_EMDASH_FOCUSED_CAS_AND_CATEGORICAL_ENGINE_PLAN.md)
already makes the CAS useful independently, with proofs as a consumer and
CAP/homalg-inspired categorical programming above efficient algebra operations.
The [delegation plan](TYPESCRIPT_EMDASH_PROOF_CAS_DELEGATION_PLAN.md) already joins
named formal goals to typed computation and explicit adoption.

"OSCAR + typed proof assistant" is a useful direction, not a present breadth,
performance or metatheory claim. Existing profile/variance qualifications and
the separately deferred integration/repair work remain unchanged.

## What the OSCAR comparison establishes

OSCAR combines GAP, Singular, Polymake and the ANTIC/Hecke/Nemo/AbstractAlgebra
ecosystem through Julia, with common mathematical interfaces and domain-specific
algorithms. Julia is both an implementation language and a scientific-computing
host with native-library access. [Official overview](https://oscar-system.github.io/oscar-website/about/).

This interoperability has concrete representation contracts. OSCAR separates
Julia element types from their runtime mathematical parents, and its GAP
integration exposes maps between supported rings/fields and their elements.
The documentation also records representation and caching limitations.
[Parent model](https://docs.oscar-system.org/v1/General/faq/),
[GAP integration](https://docs.oscar-system.org/v1/DeveloperDocumentation/gap_integration/).
Singular.jl supports AbstractAlgebra/Nemo coefficient interfaces, but its
interpreter bridge has explicit restrictions; there is no universal conversion
of arbitrary mathematical objects.
[Coefficient interfaces](https://oscar-system.github.io/Singular.jl/dev/nemo/),
[interpreter boundary](https://oscar-system.github.io/Singular.jl/latest/caller/).

The plotting intuition is valid. The 2026 paper
[Drawing real plane algebraic curves in OSCAR](https://arxiv.org/html/2603.12985v1)
demonstrates a pipeline involving polynomial systems, algebraic solvers,
numerical methods and curve drawings. It also discusses heuristic failures
and loss of topology through floating-point rendering. This supports integrated
computation/visualization, not automatic certification of every picture.

## Corresponding responsibilities

| Responsibility | Emdash direction |
| --- | --- |
| Julia as the common user/extension language | TypeScript expressions, libraries and workspaces; ordinary functions remain appropriate for simple calculations |
| OSCAR's mathematical integration layer | Parent-aware algebra objects, operation contracts, explicit conversions/realizations and reusable computation graphs |
| Specialist algorithms and representations | Native TypeScript where useful; selected WASM/native engines or a Julia/OSCAR adapter for additional coverage |
| Visualization and documents | Browser plots, Arrowgram diagrams and existing book sources as views of the same mathematical data |
| Additional formal layer | Explicit emdash Core checking, qualified mathematical libraries, operation-specific proof bridges and Lambdapi's recorded specification/conformance roles |

TypeScript's static annotations are erased. They help author the integration
but do not validate arbitrary runtime backend data or prove its mathematics.
Runtime schemas/parents and Core checking remain distinct.
[TypeScript handbook](https://www.typescriptlang.org/docs/handbook/2/basic-types.html#erased-types).

This language choice does not supply Julia's execution model, native interfaces
or scientific ecosystem automatically. An OSCAR adapter could reuse that
ecosystem as one backend; independently wrapping or reimplementing every
cornerstone is not a prerequisite. Begin with a bounded structured operation.
Batch expensive work near its backend; optimize transport or use native handles
when measured workloads justify it. Backend handles must not become portable
mathematical identity or proof evidence.

## Existing implementation and actual gaps

| Existing owner | What it supplies and where its claim stops |
| --- | --- |
| [algebra_parent.ts](../src/v3_2/algebra_parent.ts) | Explicit runtime parent/element identity; not a proof that two differently presented structures are equivalent |
| [algebra_engine.ts](../src/v3_2/algebra_engine.ts) | Separate operations, algorithms, engines, runtime schemas, result quality, assumptions and diagnostics; `exact` is not a kernel-proof status |
| [algebra_graph.ts](../src/v3_2/algebra_graph.ts) | Typed computation topology and sequential execution; no general scheduler, persistent cache or proof semantics |
| [algebra_oracle.ts](../src/v3_2/algebra_oracle.ts) | An opt-in Singular radical-membership engine for non-authoritative differential comparison; not general GAP/OSCAR interoperability |
| [algebra_formal_delegation.ts](../src/v3_2/algebra_formal_delegation.ts) and [adoption](../src/v3_2/algebra_formal_adoption.ts) | Exact goal/realization binding, observation, checked data, checked proof-plan adoption and explicit trusted assumptions; the generic goal boundary is currently a closed depth-zero root hole |
| [research_goal_graph.ts](../src/v3_2/research_goal_graph.ts) | Derived theorem/task/decision status with different evidence policies; no execution scheduler or identity authority |
| [Native homology audit](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_FINAL_AUDIT.md) | Whole K/Q/H/connecting operations and displayed proof–CAS examples, under explicit model/normality/interpretation contracts |

The [ideal-equality adapter](../src/v3_2/algebra_formal_ideal_delegation.ts)
currently declares `trusted-selected-ideal-relations`; its positive result
produces a claim and reified coefficients, not automatically a reconstructed
proof. This is a concrete extension boundary. Do not describe the existing
bridge as a fully certified general CAS.

The missing product capability is a convenient way to construct and reuse
these objects across engines, proof developments and views. That needs a
small facade and selected adapters before another foundational framework.

## A concrete shared-object workflow

Take R = Q[x,y], f1 = y - x², f2 = xy - 1, and I = (f1,f2).
The same source-owned polynomial objects can support:

1. Exact algebra: compute with I and obtain a membership witness for x³ - 1.
2. Independent arithmetic checking of the identity
   `x³ - 1 = (-x)(y - x²) + (xy - 1)`.
3. A real-locus plot of the two input curves using an explicit Q-to-R
   interpretation, viewport and approximation policy.
4. A formal goal deriving x³ = 1 from the two supplied zero equations, if the
   selected formal ring profile and reconstruction adapter support it.

The plot is a derived view of those polynomials; no second handwritten formula
should become its authority. A GAP group would need a different mathematical
view, such as a chosen action or Cayley graph. Choosing a representation,
coefficient embedding, projection or approximation is part of the interface.

For general ideal membership, a certificate can contain coefficients a_i with
g = sum(a_i f_i). For positive radical membership it can instead exhibit
g^N = sum(a_i f_i), with N > 0. Checking these identities is distinct from
certifying a complete Gröbner basis, proving a negative answer, or certifying
the topology shown by a plot. Certificate availability is operation-specific.

There are also two distinct checks: validating a finite algebraic witness,
and deriving the corresponding formal theorem. The latter needs a faithful
interpretation and proof reconstruction or a qualified certificate checker
with its soundness argument. Reified data merely being well-typed is not enough.
Where that route is unavailable, keep the goal open or use the existing
explicit assumption policy; do not silently relabel trusted adoption.

Preserve ring characteristic, variables, monomial order, module presentations,
bases, maps and backend identity through these steps. A printed formula or an
opaque backend pointer is insufficient. OSCAR's
[serialization documentation](https://docs.oscar-system.org/v1/DeveloperDocumentation/serialization/)
likewise treats parent rings and coefficient fields as referenced objects.
Reuse Emdash's existing canonical encodings and provenance owners rather than
introducing another universal serialization schema.

## Reframing the goal assistant

The useful goal-assistant role is a mathematical work layer: help construct an
object, compute a result, inspect a counterexample, discharge a formal goal or
prepare an explanatory artifact. A goal can concern mathematical data or a
whole construction, not just a proposition. An AI assistant can propose the
decomposition and select operations; source, input checks, formal checking and
explicit assumptions determine what the results mean.

Keep the existing graphs linked but semantically separate:

- proof goals track checked terms, local contexts and missing obligations;
- computation graphs track data dependencies, operation execution and results;
- research/task goals track human intent, dependencies and approvals.

One workspace may display all three. An executed computation is not thereby
a proof, and a human-approved task is not thereby a theorem. Simple arithmetic
does not need a task node. Reuse the existing goal/delegation contracts, adding
generality only for a concrete unsupported consumer.

This is consistent with the earlier proof-assistant decisions D-PA-001,
D-PA-075 and D-PA-269: prioritize useful proof work, keep planning policy
separate from proof authority, and leave the benchmark canary parked.
Their [decision ledger](TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md)
already records the reasons. The new framing does not revive that harness.

For categorical work, preserve whole functors, adjunctions and universal maps.
A computation request should realize a selected whole operation where available;
it should not make callers repeatedly supply naturality squares or replace
the internal mathematics with external matrix equalities. The CAS realization
and higher formal profile have their own qualifications.

## Proposed first increment and stopping rule

Select one bounded polynomial/ideal workspace with one external backend,
one reusable result view and one explicit formal goal. Reuse existing native
operations as the baseline. Demonstrate stable parent-aware round trips,
inspection of the whole result/witness, rejection of a wrong parent or altered
certificate, and rechecking/invalidation after source changes. Show a useful
plot without requiring that the plot itself close a theorem.

If formal reconstruction needs unsupported owners, retain that obligation as
a named boundary instead of expanding the kernel to make the demo green.
The next natural mathematical consumer is an existing native module/homology
workflow with retained maps and assumptions. Broader resolutions, Ext and
spectral work continue through their own mathematical plans.

Stop after the selected workflow answers its product question. Functional
breadth, performance, backend portability and formal assurance are separate
dimensions of eventual OSCAR parity. No new notebook platform, plugin bus,
universal goal ontology, rewrite system or book implementation is selected.

Review evidence: current source/contracts and selected existing ledgers were
read, alongside the primary documentation and curve paper linked above.
No OSCAR installation, external backend run, benchmark, code change or aggregate
check was performed. This is a design reference, not implementation evidence.

## Follow-up: integration mechanisms and optional certification

Date: 2026-09-24. Implementation reference: `75b3ecdb`; the
[workbench plan](TYPESCRIPT_EMDASH_ALGEBRA_WORKBENCH_PLAN.md) records qualification
and the user's aggregate waiver. The original review evidence above remains
dated; the subsequent consumer executes Singular and renders a shared-object view.

The computation-first design remains the authority. Producing useful internal
objects, operations and constructions does not require proving every CAS
algorithm. Checked proof reconstruction is an optional adoption mode in the
[existing delegation plan](TYPESCRIPT_EMDASH_PROOF_CAS_DELEGATION_PLAN.md#adoption-modes),
alongside observing results, reifying typed data, and explicitly adopting an
opaque claim. The previous completion wording about deferred reconstruction
must not imply that basic CAS-to-declaration integration is missing or that
certification is the next mandatory product step.

| Capability | Existing mechanism and this consumer's status |
| --- | --- |
| Computation and reusable mathematical data | Native ideal operations and the Singular adapter consume the same parent-aware polynomial objects; returned coefficients are actual polynomial values |
| Typed internal expressions and formal statements | The existing realization/delegation route reifies coefficients and the exact equality into Core and checks their types |
| Opaque declaration without a proof body | `adoptAlgebraFormalTrustedComputation` already adds a typed opaque declaration after an explicit caller decision, records its trusted origin, and returns an ordinary goal patch/reference |
| Checked proof reconstruction | Separate optional route; no reconstruction plan is supplied by this ideal adapter |
| Complete external-output-to-formal-declaration example | Still narrower than the existing general mechanisms: this demo's formal helper executes the native CAS request; Singular's returned coefficient vector is independently checked and displayed, but is not itself fed into that formal delegation request |

A focused regression now applies the existing opaque-adoption function to this
exact `x³ = 1` goal. It verifies the exact declaration type, absent body, opaque
status, retained trusted-assumption artifact and completion relative to the new
assumption. The original environment and open proof document remain unchanged.
This tests an explicit in-memory caller action; it does not silently add an
assumption to the default demo or to the mathematical library.

Thus the demo's missing explicit adoption control, and routing the external
coefficient data through the selected reifier/delegation contract, are consumer
integration work. They are not waiting for a new proof-checking foundation or
a verified Gröbner algorithm. For new object families, their mathematical
realization and interpretation contracts still need to be supplied. Whole
internal operations remain the preferred interface; the
[native homology audit](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_FINAL_AUDIT.md)
already demonstrates richer whole constructions under explicit model contracts.

### What the OSCAR analogy now supports

The engineering assessment is that comparable integration functionality is
architecturally plausible, with a concrete route through TypeScript authoring,
runtime parents, operation contracts, explicit mathematical maps, backend
adapters and selected internal realizations. The successful polynomial consumer
is evidence for that route. It is not an established result that all OSCAR
integration mechanisms already have qualified counterparts, or that full
parity across them is assured.

OSCAR's own integration uses explicit conversion maps for supported rings and
fields, with recorded caching and representation differences; Singular.jl also
documents interpreter limitations. These are useful standards for defining
specific interoperability contracts, rather than expecting automatic conversion
of every mathematical object.
[GAP integration](https://docs.oscar-system.org/v1/DeveloperDocumentation/gap_integration/),
[Singular interpreter boundary](https://oscar-system.github.io/Singular.jl/latest/caller/).
Julia's native multiple dispatch is another concrete host-language facility;
an analogous TypeScript API would need runtime operation/capability selection
and appropriate backend execution instead of obtaining those semantics from
static annotations.
[Julia methods](https://docs.julialang.org/en/v1/manual/methods/).

The following mechanism-level questions remain beyond this experiment:

- bidirectional exchange of richer rings, fields, modules, maps and whole
  constructions, including explicit changes of presentation;
- composition across two genuinely different external engines using retained
  mathematical identity and maps;
- persistent foreign-object lifetime, caching and serialization with shared
  parents, session/revision changes and failures;
- callback/asynchronous execution and extension contracts where needed; and
- measured transport, batching and native/WASM/service costs on real workloads.

These are feasibility questions to test with selected consumers, not a newly
selected infrastructure programme. A useful next experiment would consume an
external result as typed internal data or an explicitly assumed declaration,
then reuse it in a second mathematical operation, preferably through an existing
module/homology interface. Optional proof reconstruction can be added for a
specific mathematical need. Algorithm breadth, language ergonomics, performance
and formal assurance remain separate from integration-mechanism parity.

Continuation selected (2026-09-24): the user accepted this external-result-to-
internal-reuse probe. Its scope and execution now live in the
[completed workbench continuation](TYPESCRIPT_EMDASH_ALGEBRA_WORKBENCH_PLAN.md#completed-continuation-external-result-and-internal-reuse).
The completed first consumer and its qualification remain dated evidence.

The continuation now implements that path in a separate module example:
actual Singular coefficients become typed Core matrices, one explicitly adopted
computed equation supports a whole complex assembled through existing
constructors, and its projected differential is consumed by an internal matrix
action. Core checks the terms and types; focused Lambdapi observations confirm
the retained column and action. This strengthens the mechanism evidence without
claiming full OSCAR parity, automatic certification, homology, or new standalone
TypeScript projection-reduction rules. The living plan owns exact validation.
