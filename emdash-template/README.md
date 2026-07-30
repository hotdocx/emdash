# emdash v3.2 External-Review Workbench

This directory contains the static React/Vite reviewer interface for the
TypeScript emdash v3.2 implementation. It consolidates four existing
ingredients into one client-side journey:

1. editable ordinary categorical text;
2. the checked outer-LF, ordinary-functorial, and genuinely displayed
   three-panel research report;
3. the generated current emdash book; and
4. the preserved editable minimal explicit-Core playground.

The default expression view accepts the three reviewed ordinary presets:

```text
λ^f x. (H x) (K x)
λ^f x. F x y0
G pA
```

The source is parsed and recursively resolved by the existing categorical
text adapter, lowered through the existing `CoreCategoricalProgram`, and
checked as backend-neutral explicit Core. The browser owns no second
categorical action table, checker, evaluator, or semantic profile. Edited
invalid input returns the same source-located diagnostic as the TypeScript
path.

The comparatively large categorical/report closure is loaded as a separate
Vite chunk. Loading it does not execute the report. The report runs only
after the reviewer selects **Run full research report**, with a visible
running state. Vite fingerprints and emits `../docs/emdash-book.pdf` as a
static asset.

The minimal playground still reaches the exact content-pinned
`emdash-v3.2-mvp-1` browser API and frozen `CORE_MVP_MANIFEST` through
`src/v3_2/browser_directed.ts`, which preserves the original
`src/v3_2/browser.ts` exports. The integrated entry does not mutate that
manifest. Lambdapi remains the active mathematical specification and bounded
conformance oracle. The client-side workbench does not execute Lambdapi in production.

## Run Locally

After bootstrapping the repository worktree:

```bash
./scripts/pnpmw --dir emdash-template --ignore-workspace exec vite
```

Vite reports the local URL, normally `http://localhost:5173`.

The product-facing production gate is:

```bash
./scripts/pnpmw run check:browser-reviewer
```

The historical `check:browser-directed` command remains an exact compatibility
alias. The gate runs root typecheck and lint, fixture typechecking, and the
Vite production build. App-level TypeScript does not reimpose
`noUnusedLocals`, `noUnusedParameters`, or switch-style diagnostics on the
entire imported research-library closure; those source checks remain owned by
the root package.

## Static Hosting

The deployable artifact is generated under `emdash-template/dist/`. It uses
relative asset URLs and requires no Node backend, so it is suitable for a
project subpath such as `https://hotdocx.github.io/emdash/`.

No GitHub Pages workflow, deployment, publication, custom domain, or release
is part of this implementation. Those remain separate reviewed operations.

## Exact Boundary

The current browser demonstrates:

- three editable ordinary categorical examples with expected-type-directed
  application;
- the unchanged outer dependent-LF, ordinary binder, and displayed-chain
  report;
- the generated book asset; and
- the frozen minimal Core checker example.

It does not yet provide displayed categorical text syntax, `^n`, `^fd`, or
`^nd` text resolution, arbitrary displayed telescope depth, browser-side
source acquisition, systematic groupoidal closure, or whole-library transfer
graduation. Direct typed TypeScript remains the most complete construction
surface.
