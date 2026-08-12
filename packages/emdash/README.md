# @hotdocx/emdash

`@hotdocx/emdash` is the browser-safe TypeScript distribution of emdash's
backend-neutral explicit Core and AI-native authoring infrastructure. Direct
TypeScript builders, structures, classes, instance providers, and synthesis
produce ordinary terms which are checked at the same explicit Core boundary.

```sh
pnpm add @hotdocx/emdash
```

The package has four deliberately bounded entries:

- `@hotdocx/emdash` — Core syntax, contexts, sessions, checking, evaluation,
  conversion, and the reviewed v3.2 manifest;
- `@hotdocx/emdash/authoring` — scoped outer-LF builders and compilation,
  record/structure macros, class inheritance, explicit provider scopes,
  bounded recursive instance synthesis with semi-output premise scheduling,
  output-parameter inference, and saturated class calls; and
- `@hotdocx/emdash/workspace` — explicit proof plans and artifacts plus
  browser-safe declaration/fragment workspaces and canonically ordered
  multi-module proof-development catalogs, including exact canonical-data
  reconstruction for materialized proof sources. Selected-constructor syntax
  expands to the ordinary checked `apply` proof plan; it adds no tactic state
  or serialized plan tag. Contextual `have` is a serialized plan node: its
  checked fact remains an explicit named obligation even when the continuation
  does not use it. Root-scoped typed `refine` templates are management-only
  term-placeholder data which expand immediately to those `have` nodes plus
  `exact`; Pi/lambda binder annotations remain ordinary meta-free Core, and
  no template or process-local meta enters canonical source. Fresh plan replay
  separately exposes a portable direct coupling graph over stable named goals;
  the canonical v2 proof artifact remains unchanged. The additive proof
  simplifier accepts explicit ordered global equality theorems, performs
  bounded deterministic root-target rewriting, and expands its checked
  backward transports to the same existing `have` plus `exact` nodes. The
  accessible-premise index reconstructs one exact module closure, exposes
  root-local and direct-public declarations with structured scope reasons,
  and searches exact IDs and bounded structural Core fingerprints without
  claiming theorem applicability. The obvious-proof provider consumes that
  exact scope and proposes immutable replacements for one named hole: checked
  global `exact` candidates or one ordinary `apply` with explicit named
  premise holes. It returns all bounded candidates and fresh replay evidence;
  it does not recursively discharge goals or retain a tactic session. The
  semantic-development diff reconstructs and checks two declaration
  revisions, reports exact declaration/source changes plus structural
  dependency impact, and conservatively classifies unchanged proof source for
  recheck without executing a possibly broken current proof or proposing a
  repair. The selected-proof maintenance layer composes that impact with fresh
  replay of one exact proof. It projects stable rejection diagnostics and,
  only for a successfully replayed named hole, delegates checked `exact` and
  one-step-`apply` candidates to the existing bounded provider. Candidate
  acceptance returns a stale-safe patch, patched inert plan, and fresh replay;
  it does not silently persist source or claim to refresh caller-supplied
  fingerprints.
  The mixed-fragment proof attachment reconstructs the selected module's
  exact transitive declaration/runtime closure before every replay. Its proof
  request contains inert source, dependency, and runtime fingerprints but no
  executable runtime input; the checker derives the reviewed runtime from the
  reconstructed fragments and rejects closure or runtime drift.
  The companion fragment-proof development catalog compiles one directly
  authored TypeScript fragment workspace, canonically orders independent
  proofs, freshly replays each exact runtime closure, and exposes deterministic
  aggregate status, lookup, and named open goals without a resident prover.
  The research-goal profile keeps theorem, task, and decision evidence
  distinct, freshly replays checked-proof evidence, and derives status across
  finite `requires` and grouped `one-of` dependencies. Its companion
  host-neutral view exposes only stable nodes, derived explanations, edges,
  and status counts: proof source, expected Core terms, evidence payloads,
  actor identities, host permissions, and action authority are deliberately
  absent. View creation replays the supplied evaluation before projection;
  validation and parsing preserve exact canonical JSON for renderers and
  lightweight hosts; and
- `@hotdocx/emdash/benchmark` — the browser-safe immutable proof-agent case,
  suite, attempt, run, and report evaluator; strict canonical interchange;
  and a fixed six-track, ten-case reference corpus. Nine reference patches
  pass fresh TypeScript/emdash replay and one genuine ambiguity case abstains.
  These are reproducible baselines, not proof authority, committed source,
  agent-performance measurements, or a leaderboard. The evaluator invokes no
  provider, model, network, filesystem adapter, or proof server.

```ts
import { CoreChecker } from '@hotdocx/emdash';
import {
  CoreLfScopedBuilder,
  CORE_LF_INSTANCE_SYNTHESIS_PROFILE,
  CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE,
  CORE_LF_INSTANCE_SCOPE_PROFILE,
  synthesizeCoreLfInstance,
  synthesizeCoreLfInstanceByRoles,
} from '@hotdocx/emdash/authoring';
import {
  CORE_LF_DEVELOPMENT_DIFF_PROFILE,
  CORE_LF_DECLARATION_WORKSPACE_PROFILE,
  CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE,
  CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE,
  CORE_LF_PREMISE_INDEX_PROFILE,
  CORE_LF_PROOF_DEVELOPMENT_PROFILE,
  CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE,
  CORE_OBVIOUS_PROOF_PROVIDER_PROFILE,
  CORE_PROOF_PLAN_PROFILE,
  CORE_PROOF_PLAN_MACRO_PROFILE,
  CORE_PROOF_PLAN_PATCH_PROFILE,
  CORE_PROOF_GOAL_COUPLING_PROFILE,
  CORE_PROOF_REFINE_TEMPLATE_PROFILE,
  CORE_PROOF_SIMPLIFIER_PROFILE,
  CORE_RESEARCH_GOAL_GRAPH_PROFILE,
  CORE_RESEARCH_GOAL_VIEW_PROFILE,
  coreProofPlanConstructor,
  coreProofPlanHave,
  coreProofPlanRefine,
  coreProofTemplatePlaceholder,
  compareCoreLfProofDevelopmentSources,
  compileCoreLfFragmentProofDevelopment,
  compileCoreLfFragmentWorkspaceProofDocument,
  createCoreProofPlanHoleReplacement,
  createCoreLfAccessiblePremiseIndex,
  createCoreLfFragmentProofDevelopment,
  createCoreLfFragmentWorkspaceProofFingerprint,
  createCoreLfFragmentWorkspaceProofFingerprintForWorkspace,
  createCoreLfFragmentWorkspaceProofRuntimeFingerprint,
  createCoreLfProofDevelopment,
  createCoreResearchGoalView,
  parseCoreResearchGoalViewText,
  parseCoreLfProofDevelopmentSourceText,
  proposeCoreObviousProofPlanPatches,
  replayCoreObviousProofCandidate,
  serializeCoreLfDevelopmentSemanticDiff,
  serializeCoreProofGoalCouplingGraph,
  serializeCoreResearchGoalView,
  searchCoreLfAccessiblePremises,
  simplifyCoreProofPlan,
} from '@hotdocx/emdash/workspace';
import {
  CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE,
  CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE,
  createCoreLfProofAgentPublicCorpus,
  parseCoreLfProofAgentBenchmarkRunText,
  serializeCoreLfProofAgentBenchmarkRun,
} from '@hotdocx/emdash/benchmark';

const terms = new CoreLfScopedBuilder();
void CORE_LF_INSTANCE_SYNTHESIS_PROFILE;
void CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE;
void synthesizeCoreLfInstance;
void synthesizeCoreLfInstanceByRoles;
void CORE_LF_PROOF_DEVELOPMENT_PROFILE;
void CORE_LF_DEVELOPMENT_DIFF_PROFILE;
void CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE;
void CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE;
void CORE_LF_PREMISE_INDEX_PROFILE;
void CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE;
void CORE_OBVIOUS_PROOF_PROVIDER_PROFILE;
void CORE_PROOF_PLAN_PROFILE;
void CORE_PROOF_PLAN_MACRO_PROFILE;
void CORE_PROOF_PLAN_PATCH_PROFILE;
void CORE_PROOF_GOAL_COUPLING_PROFILE;
void CORE_PROOF_REFINE_TEMPLATE_PROFILE;
void CORE_PROOF_SIMPLIFIER_PROFILE;
void CORE_RESEARCH_GOAL_GRAPH_PROFILE;
void CORE_RESEARCH_GOAL_VIEW_PROFILE;
void coreProofPlanConstructor;
void coreProofPlanHave;
void coreProofPlanRefine;
void coreProofTemplatePlaceholder;
void compareCoreLfProofDevelopmentSources;
void compileCoreLfFragmentProofDevelopment;
void compileCoreLfFragmentWorkspaceProofDocument;
void createCoreProofPlanHoleReplacement;
void createCoreLfAccessiblePremiseIndex;
void createCoreLfFragmentProofDevelopment;
void createCoreLfFragmentWorkspaceProofFingerprint;
void createCoreLfFragmentWorkspaceProofFingerprintForWorkspace;
void createCoreLfFragmentWorkspaceProofRuntimeFingerprint;
void createCoreLfProofDevelopment;
void createCoreResearchGoalView;
void parseCoreResearchGoalViewText;
void parseCoreLfProofDevelopmentSourceText;
void proposeCoreObviousProofPlanPatches;
void replayCoreObviousProofCandidate;
void serializeCoreLfDevelopmentSemanticDiff;
void serializeCoreProofGoalCouplingGraph;
void serializeCoreResearchGoalView;
void searchCoreLfAccessiblePremises;
void simplifyCoreProofPlan;
void CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE;
void CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE;
void createCoreLfProofAgentPublicCorpus;
void parseCoreLfProofAgentBenchmarkRunText;
void serializeCoreLfProofAgentBenchmarkRun;
```

This package does not parse structure or class declarations, add class nodes
to Core, keep process-global proof state, run Lambdapi, or provide filesystem,
network, host-module execution, or CLI adapters. In particular, the package
publishes no npm bin or install hook; the repository's stateless benchmark
command is an outer reference adapter. Canonical proof source is a
portable explicit-Core data envelope, not an emdash term/declaration parser or
an implicit `*.emdash.ts` import. Lambdapi remains an optional
development-time conformance route; the production path here is the
TypeScript checker.

The source and development documentation are in the
[emdash repository](https://github.com/hotdocx/emdash). The accompanying book
is archived at [doi:10.5281/zenodo.21544186](https://doi.org/10.5281/zenodo.21544186).
