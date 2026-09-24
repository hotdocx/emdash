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
