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
  browser-safe declaration and fragment workspaces.

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
} from '@hotdocx/emdash/workspace';

const terms = new CoreLfScopedBuilder();
void CORE_LF_INSTANCE_SYNTHESIS_PROFILE;
void CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE;
void synthesizeCoreLfInstance;
void synthesizeCoreLfInstanceByRoles;
```

This package does not parse structure or class declarations, add class nodes
to Core, keep process-global proof state, run Lambdapi, or provide filesystem,
network, and CLI adapters. Lambdapi remains an optional development-time
conformance route; the production path here is the TypeScript checker.

The source and development documentation are in the
[emdash repository](https://github.com/hotdocx/emdash). The accompanying book
is archived at [doi:10.5281/zenodo.21544186](https://doi.org/10.5281/zenodo.21544186).
