# Polynomial package consumer with Vega-Lite

This is an ordinary TypeScript application consuming the locally packed
`@hotdocx/emdash/algebra` entry and the existing Vega 5 / Vega-Lite 5 ecosystem.
It has its own dependency graph and imports no repository source. It is a
fixture, not another contributor workspace package or a published release.

From the repository root:

```bash
node packages/emdash/scripts/prepare-polynomial-vega.mjs
```

The command builds and packs Emdash, copies this source fixture to a fresh
temporary directory, installs the tarball and pinned dependencies with pnpm
offline, typechecks/builds the application and runs its focused tests. It
prints the consumer directory, artifact SHA-256 and command for serving it:

```bash
./scripts/pnpmw --dir /tmp/emdash-polynomial-vega-EXAMPLE start
```

Use the actual printed directory in place of `EXAMPLE`, then open
`http://127.0.0.1:4178`. The server binds only to localhost. Run
`node serve.mjs PORT` from the generated directory to select another port.
Stop it with Ctrl-C.
Generated bundles, the dependency graph, lockfile, tarball and `artifact.json`
stay in that temporary directory. The receipt hashes the tarball, fixture
sources, generated dependency lock and browser bundle. Do not install dependencies in this source
fixture. A fresh contributor checkout must first use the repository's normal
bootstrap to populate the shared pnpm store.

`--tarball FILE` consumes a specific already built artifact without rebuilding
Emdash. `--output NEW_DIRECTORY` retains the consumer at a chosen new path;
existing directories are rejected. Offline dependency failures should be
resolved through the normal pinned workspace bootstrap, without borrowing
another checkout's `node_modules`. The previously published npm `0.3.0` lacks
the additive `/algebra` entry; matching version strings do not identify the
new local artifact. No publishing credential is needed.

## Mathematical and rendering flow

`model.ts` constructs R=Q[x,y], `(y-x², xy-c)` and the query `x³-c` from one
exact rational parameter. The existing bounded reference algorithm returns
membership coefficients, and the independent exact arithmetic checker
reconstructs their combination. The same input goes to the existing bounded
sampler. `curveSpec` merely turns its segments into ordinary Vega-Lite rule
marks; it contains no second formula or custom curve renderer.

The parameter may be an integer or fraction with a positive denominator.
The input is capped at 512 characters. Three fixed finite windows bound
sampling. Numeric interpretation can fail for exact values that remain valid
for computation, so the exact calculation survives an unavailable plot.
Curves are approximate: sampling can miss components, tangencies and
singularities, and ambiguous cells are omitted. No proof goal, formal adoption,
kernel computation or topology certificate is part of this application.

`main.ts` is ordinary DOM/TypeScript application code. Input edits immediately
invalidate the old calculation/view; Apply computes the new source. Window
changes and resizes resample/render the current calculation. Vega renders into
a detached container until the current revision accepts it. `plot-slot.ts`
disposes stale asynchronous renders and retires previous views. The exact
calculation and mounted chart carry matching source identities.

## Qualification

The five fixture tests cover actual headless Vega-Lite/SVG rendering,
source-derived segment rows, source/viewport changes, unsupported numeric
interpretation, controlled out-of-order render completion and invalidation,
and the bundle's installed-package dependency closure. Tests run against the
prepared consumer and its tarball, not repository-relative imports.

The package's independent packed-install check owns ESM/CJS, public declarations
and the computation-only browser boundary. Desktop/mobile interaction checks
and exact checkpoint/artifact evidence live in
`docs/TYPESCRIPT_EMDASH_ALGEBRA_WORKBENCH_PLAN.md` in the contributor repository.
The package's formal profiles and the sampler's limitations remain unchanged.
