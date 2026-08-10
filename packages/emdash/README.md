# @hotdocx/emdash

`@hotdocx/emdash` is the browser-safe TypeScript distribution of emdash's
backend-neutral explicit Core and AI-native authoring infrastructure. Direct
TypeScript builders, structures, classes, instance providers, and synthesis
produce ordinary terms which are checked at the same explicit Core boundary.

```sh
pnpm add @hotdocx/emdash
```

The package has three deliberately bounded entries:

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
  no template or process-local meta enters canonical source.

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
  CORE_LF_DECLARATION_WORKSPACE_PROFILE,
  CORE_LF_PROOF_DEVELOPMENT_PROFILE,
  CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE,
  CORE_PROOF_PLAN_PROFILE,
  CORE_PROOF_PLAN_MACRO_PROFILE,
  CORE_PROOF_REFINE_TEMPLATE_PROFILE,
  coreProofPlanConstructor,
  coreProofPlanHave,
  coreProofPlanRefine,
  coreProofTemplatePlaceholder,
  createCoreLfProofDevelopment,
  parseCoreLfProofDevelopmentSourceText,
} from '@hotdocx/emdash/workspace';

const terms = new CoreLfScopedBuilder();
void CORE_LF_INSTANCE_SYNTHESIS_PROFILE;
void CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE;
void synthesizeCoreLfInstance;
void synthesizeCoreLfInstanceByRoles;
void CORE_LF_PROOF_DEVELOPMENT_PROFILE;
void CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE;
void CORE_PROOF_PLAN_PROFILE;
void CORE_PROOF_PLAN_MACRO_PROFILE;
void CORE_PROOF_REFINE_TEMPLATE_PROFILE;
void coreProofPlanConstructor;
void coreProofPlanHave;
void coreProofPlanRefine;
void coreProofTemplatePlaceholder;
void createCoreLfProofDevelopment;
void parseCoreLfProofDevelopmentSourceText;
```

This package does not parse structure or class declarations, add class nodes
to Core, keep process-global proof state, run Lambdapi, or provide filesystem,
network, host-module execution, and CLI adapters. Canonical proof source is a
portable explicit-Core data envelope, not an emdash term/declaration parser or
an implicit `*.emdash.ts` import. Lambdapi remains an optional
development-time conformance route; the production path here is the
TypeScript checker.

The source and development documentation are in the
[emdash repository](https://github.com/hotdocx/emdash). The accompanying book
is archived at [doi:10.5281/zenodo.21544186](https://doi.org/10.5281/zenodo.21544186).
