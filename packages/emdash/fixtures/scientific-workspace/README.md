# Emdash Scientific Workspace

This portable TypeScript project computes exact polynomial membership, reuses
its actual coefficients in a native complex, and derives a curve plot from
the same input. Edit `input.json` or the authored TypeScript directly.

`workspace.program.json` declares the runtime and all execution inputs.
GetPaidX can inspect it and run the `compute` or `reuse` task through its generic
program tools. `reuse` reads `retained.json` and checks it against the current
input; it does not rerun membership or replace the coefficient vector. Copy
a completed run's retained artifact into that input when continuing a study.

Local replay uses the manifest's exact Node version:

```bash
node run-local.mjs compute ./results
node run-local.mjs reuse ./reused
```

`result.json` carries the exact result and native construction. `plot.svg` is
an approximate real-locus view; it does not certify topology. A nonmember
retains its remainder and plot without constructing a complex.

An optional internal mode uses the existing qualified Core construction and
records one explicit computed-equation assumption:

```bash
node run-local.mjs compute ./internal-results '{"internal":true,"adoptionReason":"Use this computed zero-composition equation as an explicit assumption."}'
```

The whole complex and its action are transparent definitions, and Core checks
their types relative to the adopted equation. This does not certify the CAS
implementation or add a new standalone projection-reduction qualification.
The formal action on a supplied argument is distinct from the reported native
image at one.

The bundled library and its declaration closure are under `vendor/`.
`vendor/build.json` pins the source content, toolchain and runtime bundle.
Declaration files support authoring and are excluded from the runtime snapshot.
The same source project runs locally and in a cloud workspace. Generated output
and conversation history are views and records of that source.

The cloud preview shows equations, exact results, the complex, an approximate
plot, source editing and recent executions. Its controls use the existing
authenticated workspace execution service. Plot zoom changes only the view.
Older results are labelled when the declared source revision differs.

`Export this run` downloads the captured source, parameters, runtime pins and
artifacts as a ZIP. Unpack it and run `node replay.mjs` with the recorded Node
version. The replay checks source hashes and writes a new `replayed-artifacts`
directory. It does not export workspace credentials or session identifiers.

For a local read-only view after computing into `./results`:

```bash
EMDASH_LOCAL_VIEW=1 node server.mjs
```

Open the loopback address on port 4173. This local view has no second executor;
use the local program or Codex tools to compute and refresh the page afterward.
