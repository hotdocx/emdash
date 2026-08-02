# emdash v3.2 External-Review Workbench

This directory contains the static React/Vite reviewer interface for the
TypeScript emdash v3.2 implementation. It consolidates four existing
ingredients into one client-side journey:

1. ten editable categorical examples across the reviewed `^f`, `^n`, `^fd`,
   and `^nd` modes;
2. the checked outer-LF, ordinary-functorial, and genuinely displayed
   three-panel research report;
3. the concise overview paper and generated current emdash book; and
4. the preserved editable minimal explicit-Core playground.

Representative expression presets include:

```text
λ^f x. (H x) (K x)
λ^f x. F x y0
G pA
λ^n k : K. (FF k) (s k)
λ^fd (a : A; b : B, c : C; d : D). fibrePair b c
λ^nd k : K. composeCells (theta k) (eta k)
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
running state. The report retains its original pre-browser graduation
boundary; the interface labels that provenance rather than rewriting the
historical component report. Vite fingerprints and emits
`../docs/emdash3_2.pdf` and `../docs/emdash-book.pdf` as distinct static
assets.

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

The root `.github/workflows/pages.yml` builds this standalone fixture from
`main`, uploads only `dist/`, and deploys it with the official GitHub Pages
Actions route. No generated `gh-pages` branch or committed `dist/` is needed.

## Exact Boundary

The current browser demonstrates:

- twelve editable categorical examples across `^f`, `^n`, `^fd`, and `^nd`,
  with expected-type-directed action selection and source diagnostics;
- qualified depth-generic finite Hom-category recursion over reviewed
  categorical roots;
- the unchanged outer dependent-LF, ordinary binder, and displayed-chain
  report;
- the overview paper and generated book assets; and
- the frozen minimal Core checker example.

It does not provide arbitrary mixed introduction, unsupported variance DAGs,
displayed contexts outside the qualified canonical grammar, the remaining
displayed structural-constructor syntax, browser-side source acquisition,
systematic groupoidal closure, or whole-library transfer graduation. Direct
typed TypeScript remains the most complete construction surface.
