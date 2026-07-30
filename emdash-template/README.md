# emdash v3.2 Browser Playground

This directory contains a standalone React/Vite playground for the
browser-safe emdash v3.2 TypeScript Core API. It preserves the editable
minimal-Core playground and adds a fixed outer dependent-LF demonstration.
Both use session-local checking and the reviewed TypeScript runtime; neither
exposes the deleted global-state prototype or a legacy compatibility API.

The playground runs the exact content-pinned `emdash-v3.2-mvp-1` deployed
profile (16 owners and three runtime rules). Its browser barrel exports the
deep-frozen `CORE_MVP_MANIFEST` so consumers can inspect that identity. The
TypeScript checker/evaluator is authoritative only for this profile and does
not execute Lambdapi in production. Lambdapi remains the repository's active
mathematical specification and mandatory shared-corpus CI/subject-reduction
oracle.

The additive `browser_directed.ts` entry also runs the already reviewed
root-only `emdash-v3.2-dttlf-directed-1` dependent Sigma-telescope witness in
the browser. It is an opt-in demonstration, not a change to the frozen MVP
manifest and not a categorical-browser promotion. The additive entry
re-exports the frozen `src/v3_2/browser.ts` API rather than modifying or
replacing it.

It can be run locally with Vite or deployed as a static client-side site.
Sandpack compatibility is not a requirement. The production build uses
relative asset paths so it can be hosted below a project path such as
`https://hotdocx.github.io/emdash/` without a Node backend.

## Running Locally with Vite

This is the recommended way to work on the playground UI itself. The local Vite server uses Hot Module Replacement (HMR) for a fast development experience.

After bootstrapping the repository worktree, start the development server from
the repository root:

```bash
./scripts/pnpmw --dir emdash-template --ignore-workspace exec vite
```

Vite starts a local server at the URL it reports (usually
`http://localhost:5173`). The local application resolves
`../src/v3_2/browser_directed.ts` through `src/emdash_api.ts`.

From the repository root, the bounded production gate is:

```bash
./scripts/pnpmw run check:browser-directed
```

## Static Hosting

Run the production gate from the repository root:

```bash
./scripts/pnpmw run check:browser-directed
```

The deployable site is generated under `emdash-template/dist/`. Its HTML,
JavaScript, and CSS are self-contained static assets with relative URLs. A
GitHub Pages workflow may later upload that directory as its artifact, but
workflow creation and publication are separate reviewed operations and are
not performed by the browser implementation itself.

No backend is needed for the current functionality. The browser executes the
same TypeScript checker/evaluator and immutable runtime data locally. A future
backend would be justified only by a separately selected capability that
cannot remain client-side, not by the present LF demo.

The build contains no ambient global reset, legacy parser, D0/D1 category
API, Node builtin, or Lambdapi process dependency. The editable example
prints `CORE_MVP_MANIFEST.revision` before checking a category-polymorphic
identity. The fixed dependent view separately prints its opt-in continuation
identity, explicit Core, inferred/reduced types, reduction trace, and
wrong-family diagnostic.
