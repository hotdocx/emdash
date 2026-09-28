# Emdash Algebra Goal Assistant

Date: 2026-09-26
Reviewed: 2026-09-28
Status: user-selected product orientation; implementation remains profile-specific

**Emdash helps people do mathematics: express a goal, construct mathematical
objects, compute, explore and reuse results, while delegating routine
bookkeeping to the language and assistant.** Computation and internal/synthetic
expression are the primary experience. Proof development and certification
remain useful capabilities when the mathematical work calls for them.

The broader [scientific computing strategy](EMDASH_SCIENTIFIC_COMPUTING_STRATEGY.md)
now places this assistant within an open-source, AI-native, cloud-capable
TypeScript scientific computing system. Algebra is the first delivered
workflow. Future numerical, PDE and dynamics capabilities should connect
scientific models, computation, formal theory and visualization through usable
mathematical interfaces. Proof development concerns that mathematics; verifying
every backend algorithm is not a prerequisite.

Local use remains independently useful. GetPaidX/LastRevision is the intended
commercial cloud/community path, with its existing plugin supplying platform
access and proposed generic workspace execution of TypeScript/Emdash programs.
The [execution review](EMDASH_WORKSPACE_EXECUTION_ARCHITECTURE_REVIEW_2026-09-28.md)
keeps mathematical library methods independent of platform tools/routes.
The strategy reviews inline cards, a browser research workspace and
conversation-driven use over the
same durable source. These are design recommendations, not completed cloud/UI
qualification.

The [Codex plugin plan](EMDASH_ALGEBRA_GOAL_ASSISTANT_PLUGIN_PLAN.md) turns this
orientation into a local delivery path. The installed plugin now supports a
bounded polynomial workspace, exact computation, derived views and whole
native/internal complex reuse. Its [runtime guide](../plugins/emdash/README.md)
describes the supported workflow. Existing mathematical and
qualification authority remains with the
[elaborator handoff](TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md), active Lambdapi
owners and their scoped plans.

## Product emphasis

The normal user request is a mathematical task: calculate a quotient,
construct a map or complex, compare presentations, explore a family, explain
an obstruction, or continue a research calculation. The assistant should
produce usable mathematical objects and explanations, and help with the next
construction. A request need not begin as a theorem or end in a closed proof.

This is a priority for the product, not an empirical claim that a fixed
percentage of mathematicians value certification. Mathematical proof is also
conceptual reasoning and discovery; it is broader than checking software for
implementation bugs. The name **algebra goal assistant** communicates the
broader workflow without redefining proof or discarding existing proof tools.

The practical distinction from systems designed around an earlier interaction
model is an agent-oriented interface from the outset: inspectable source,
meaningful mathematical operations, structured results, resumable files and
precise diagnostics. It does not imply that Lean or existing CAS systems cannot
be used with AI agents. Their algorithms and interfaces can remain useful
backends or references.

## Computational and internal

Computation supplies actual values, maps, presentations and constructions.
Internal/synthetic language lets the user work with those constructions through
their mathematical interfaces. A whole complex, functor or universal operation
should remain available for further use; the system should manage the relevant
components, context and dependency bookkeeping where its supported interfaces
permit that.

The assistant and adapters should derive routine identifiers, source hashes,
dependency closures, display data and artifact locations. Ask the user for
mathematically significant choices when necessary: a coefficient domain,
interpretation, presentation, universal property or intended assumption. Avoid
making users copy opaque IDs, coordinate tables or checker metadata merely to
express a mathematical idea.

The [recent workbench](TYPESCRIPT_EMDASH_ALGEBRA_WORKBENCH_PLAN.md) provides two
concrete foundations: the same polynomial source supports computation and a
Vega-Lite view; actual external coefficients can also become typed internal
module data, a whole constructed complex and a further internal action. The
second path records its required computed-equation assumption explicitly.
Neither path establishes general homology computation or complete library
transfer. The selected formal interpretation is narrower than the native
rational-polynomial computation, and opaque signature mirrors do not qualify
new TypeScript projection reductions.

## TypeScript and the assistant

TypeScript is the host programming and authoring environment. Ordinary
functions, packages and application code are available alongside Emdash's
mathematical APIs. Explicit Core is the internal mathematical/proof language.
The assistant should help write concise source using existing builders and
whole operations, rather than requiring a new textual language or exposing
raw Core trees as the normal interaction.

Codex supplies the agent conversation and access to execution tools. The Emdash
plugin should supply mathematical workflows, capability discovery and a portable
runtime over the existing library. It does not need a second model backend or
another chat product merely to become usable. Files and mathematical artifacts
remain recoverable independently of a particular chat session.

## Results and goals

Keep the mathematical status of a result accurate without turning status
bookkeeping into the user's main task. Exact computational results,
approximations, explicit assumptions, conjectures and checked proofs have
different meanings. Type checking can prevent incompatible domains, maps or
contexts and support expression/reuse even when no proof of the underlying
algorithm is requested. An exact arithmetic result does not automatically
become a theorem checked by Core.

There are three distinct uses of “goal”:

- A user's mathematical/research goal organizes the work and useful outcomes.
- An Emdash proof goal is a typed obligation handled by the existing proof
  owners when that activity is selected.
- A Codex persistent goal manages the assistant's ongoing work and recovery.

The existing research-goal graph can organize supported theorem/task/decision
dependencies. Its evidence rules should remain intact. Calling the product a
goal assistant does not require every computation to become a proof node, or
authorize marking a task satisfied with invented human approval.

## Success criteria

- A user states a mathematical goal in ordinary language, reviews the
  meaningful choices, and receives reusable mathematical source and results.
- The assistant computes and constructs with the supported objects, rather
  than returning only prose or a certificate about an isolated computation.
- Editing an input updates or invalidates its dependent outputs; a new session
  can resume from the same files without reconstructing hidden chat state.
- Views, diagrams and documents derive from the mathematical source and use
  ordinary ecosystem libraries.
- Optional proof work uses the existing checking/adoption contracts. Unsupported
  mathematics is identified at its actual boundary, without silently replacing
  the requested interpretation or weakening a claim.

This orientation extends the computation-first
[CAS plan](TYPESCRIPT_EMDASH_FOCUSED_CAS_AND_CATEGORICAL_ENGINE_PLAN.md) and the
file-based [AI-native workspace plan](TYPESCRIPT_EMDASH_AI_NATIVE_WORKSPACE_AND_PROOF_PLAN.md).
Existing proof APIs, plan IDs and serialized protocol names keep their precise
technical meaning. No wholesale rename or mathematical foundation migration
is implied by the product name.
