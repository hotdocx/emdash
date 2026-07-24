# emdash v3.2 Sandpack Playground

This directory contains a standalone React/Vite playground for the
browser-safe emdash v3.2 TypeScript Core API. It uses session-local contexts,
metavariables, checking, and the reviewed runtime fragment; it does not expose
the deleted global-state prototype or a legacy compatibility API.

The playground runs the exact content-pinned `emdash-v3.2-mvp-1` deployed
profile (16 owners and three runtime rules). Its browser barrel exports the
deep-frozen `CORE_MVP_MANIFEST` so consumers can inspect that identity. The
TypeScript checker/evaluator is authoritative only for this profile and does
not execute Lambdapi in production. Lambdapi remains the repository's active
mathematical specification and mandatory shared-corpus CI/subject-reduction
oracle.

It can be run in two ways:
1.  Locally for development and testing using Vite.
2.  As a template within a Sandpack instance for embedding in web applications like `hotdocx`.

## Running Locally with Vite

This is the recommended way to work on the playground UI itself. The local Vite server uses Hot Module Replacement (HMR) for a fast development experience.

**Prerequisites:**

* Node.js and npm (or pnpm/yarn) installed.

**Steps:**

1.  Navigate to this directory from the project root:
    ```bash
    cd emdash-template
    ```
2.  Install the dependencies:
    ```bash
    npm install
    ```
3.  Start the development server:
    ```bash
    npx vite
    ```
Vite starts a local server at the URL it reports (usually
`http://localhost:5173`). The local application resolves
`../src/v3_2/browser.ts` through `src/emdash_api.ts`.

## Using as a Sandpack Template

This template can also run inside
[Sandpack](https://sandpack.codesandbox.io/). Construct its virtual file map
from the template and the browser-safe v3.2 dependency tree.

Sandpack cannot resolve files outside its virtual root, so the host
application must copy the v3.2 modules and adjust the one bridge path.

**Procedure:**

1. **Collect template files.** Map the files under `emdash-template` into the
   Sandpack root, excluding generated directories such as `node_modules` and
   `dist`.

   * `emdash-template/index.html` → `/index.html`
   * `emdash-template/package.json` → `/package.json`
   * `emdash-template/src/App.tsx` → `/src/App.tsx`

2. **Collect the v3.2 browser dependency tree.** Copy the TypeScript modules
   reachable from `src/v3_2/browser.ts`, preserving their directory:

   * `src/v3_2/browser.ts` → `/src/v3_2/browser.ts`
   * its relative v3.2 imports → the corresponding `/src/v3_2/*.ts` paths

   Do not package `probe.ts`, the differential harnesses, or other
   process/filesystem-backed conformance tooling. The browser barrel is the
   reviewed boundary.

3. **Adjust the API bridge.** In
   `emdash-template/src/emdash_api.ts`, replace
   `../../src/v3_2/browser.js` with `./v3_2/browser.js`, then install that
   content as `/src/emdash_api.ts`.

This produces a self-contained browser project with no ambient global reset,
legacy parser, D0/D1 category API, or Node-only Lambdapi process dependency.
The included example prints `CORE_MVP_MANIFEST.revision` before checking a
category-polymorphic identity, so a copied template retains an observable
`emdash-v3.2-mvp-1` profile boundary.
