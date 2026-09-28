# Emdash algebra goal assistant

The local runtime helps an agent compute, view and reuse mathematical data in
ordinary files. This directory is the source of the locally installed Codex
plugin governed by the [living plan](../../docs/EMDASH_ALGEBRA_GOAL_ASSISTANT_PLUGIN_PLAN.md). Public distribution
and cloud delivery are separate milestones.

The [scientific computing strategy](../../docs/EMDASH_SCIENTIFIC_COMPUTING_STRATEGY.md)
places this algebra workflow within the broader TypeScript scientific-computing
direction. It recommends optional GetPaidX cloud execution and inline/browser
views over the same source and results. Those adapters remain proposed; this
runtime currently supplies local CLI/STDIO operations.

## Local Codex installation

Build the runtime first, then register this repository marketplace and install:

```bash
codex plugin marketplace add /absolute/path/to/emdash-checkout
codex plugin add emdash@personal
```

The repository marketplace uses the scaffold's `personal` name and remains
separate from Arrowgram/GetPaidX's `hotdocx` marketplace. Its source lives in
this repository's `.agents/plugins/marketplace.json`; no home marketplace is
created. Use the actual registered checkout path. Start a fresh Codex session
after installation or a plugin update so it picks up the installed skill/tools.

The local `emdash-local` server starts the bundled runtime through
`scripts/start-mcp.mjs`. It requires Node on the host PATH, not a GetPaidX
account or a new model API key. Each MCP tool takes an explicit absolute
mathematics workspace root; the server's cwd can be the installed cache and
must not be mistaken for the user's workspace. The installed plugin directory
is rejected as a data root. These are local user-process file capabilities;
they are not a hosted authorization boundary.

The SDK adapter projects the same command catalog and runs fixed bundled
workers with a 30-second deadline, a 512 MiB V8 heap limit, bounded input/output
and at most two concurrent operations. Cancellation or transport closure
terminates the corresponding worker. After an interrupted write, inspect the
workspace before retrying. No caller-provided shell command or module is executed.

The current local CLI acceptance used Codex 0.156.1 and Node 24.11.1. It verified
real installed-plugin MCP calls from a clean unrelated directory. The Codex app
uses the shared local plugin/MCP configuration; GUI invocation is not a separate
qualification claim from that CLI smoke.

## Build and use the portable runtime

From the contributor repository root:

```bash
node packages/emdash/scripts/build-goal-runtime.mjs
node packages/emdash/scripts/verify-goal-runtime.mjs
```

The generated `dist/` contains a standalone Node command, an optional authoring
module with TypeScript declarations, and `build.json` with source/bundle hashes.
The command uses Node builtins and its bundled implementation; it does not
resolve runtime imports back into the contributor checkout. The CLI is built
for Node 20+, and native TypeScript authoring was tested on Node 24.11.1.

```bash
node /path/to/plugin/dist/emdash-agent.cjs capabilities
node /path/to/plugin/dist/emdash-agent.cjs init --root /absolute/math-workspace
node /path/to/plugin/dist/emdash-agent.cjs inspect --root /absolute/math-workspace
node /path/to/plugin/dist/emdash-agent.cjs compute --root /absolute/math-workspace
node /path/to/plugin/dist/emdash-agent.cjs render --root /absolute/math-workspace
node /path/to/plugin/dist/emdash-agent.cjs construct --root /absolute/math-workspace
```

Use the actual built or installed plugin path. `init` supplies a small polynomial
relation example over Q[x,y] and refuses to overwrite existing source. `compute`
returns exact membership, retained coefficients and a remainder. `render` derives
an approximate SVG/HTML plane-curve view from the same source. Computation needs
no proof goal or adopted assumption. Numeric rendering can be unavailable while
the exact computation remains usable.

## Internal construction and further use

For a retained relation `g = a1*f1 + ... + an*fn`, native construction forms
`D = (f1,...,fn,g)` and `s = (a1,...,an,-1)`, constructs the whole complex
`R ← R^(n+1) ← R`, and applies its upper map to one. It checks `D*s = 0` by
exact arithmetic. It retains the actual coefficient choice and does not run
membership again. A valid alternate retained vector produces a distinct
construction. This does not claim a complete kernel, exactness or homology.

To additionally construct a typed internal complex and use its projected
differential, choose the explicit computed-equation route:

```bash
node /path/to/plugin/dist/emdash-agent.cjs construct \
  --root /absolute/math-workspace --mode internal \
  --reason 'Use this exact computed zero-composition equation as an explicit assumption'
```

The equivalent `emdash_construct` MCP input has `mode: "internal"` and
`adoptionReason`. Existing constructors build a transparent Core definition;
the whole object is not postulated. A second transparent definition applies
its projected differential to a supplied formal vector of rank one. This
formal argument is distinct from the native one used in `nativeImageOfOne`:
for the default example, the mathematical action is `a ↦ (-x*a,a,-a)` and
the native image at `1` is `(-x,1,-1)`.
One body-free computed-equation declaration is recorded, and Core checks the
construction/action types relative to it. Proof reconstruction and new
standalone TypeScript projection-reduction rules are not claimed.

The internal interpretation remains bounded to integer polynomials in a supplied
commutative ring. The native rational complex remains available for inputs
outside that interpretation. `.emdash/construction.json` contains the native
matrices, internal definitions and assumption/fingerprint material when selected.
Its freshness depends on both source and retained computation bytes. Serialized
Core is not trusted as proof authority; rerunning construction performs fresh
checking through the current owners.

## Source and artifacts

`emdash.goal.json` is the inert mathematical source. It names an exact rational
polynomial ring, ordered generators and a query using the existing polynomial
owner's coefficient/exponent encodings. `capabilities` supplies the example,
source schema and supported bounds. The first profile supports 1–4 ordered
variables and 1–8 generators; the plane-curve view needs two variables.

The assistant can edit this file or construct the data through ordinary
TypeScript builders and the optional `dist/authoring.cjs` module. The latter
exports the existing curated algebra API plus `createAlgebraGoalSource` and
`serializeAlgebraGoalSource`. Such a producer runs explicitly in the authorized
host. Workspace inspection and computation never import or execute user code.

For a coordinated update, inspect the source revision, then use:

```bash
node /path/to/plugin/dist/emdash-agent.cjs update \
  --root /absolute/math-workspace \
  --expected-revision sha256:THE_INSPECTED_REVISION \
  --source /absolute/new-source.json
```

The assistant carries this revision bookkeeping. A preceding source is retained
in `.emdash/history/`; `.emdash/computation.json` and the view files are derived
artifacts. Input changes make prior artifacts stale. Inspection reports freshness;
mathematical reuse independently validates the retained relation. Cache metadata
is not a proof or an attestation of an algorithm's execution.

Every command also accepts the shared inert request format through
`emdash-agent request` on stdin and returns one JSON success/error envelope.
Use the command's exit code as well as its `ok` field. The service does not run
Git, modify unrelated notes or source files, execute shell strings, contact a
model provider, or create a cloud workspace.

## Qualification

Focused source/workspace tests cover exact data, malformed inputs, stale updates,
retained result dependencies, bounded input, Unicode, symlinked owned paths,
mutation locks and view interpretation. The portable check copies `dist/` into
a fresh unrelated directory and exercises independent CLI processes, typed
authoring, source updates, computation, rendering and native/internal reuse
with no borrowed `node_modules`. The copied-plugin check uses real SDK STDIO
discovery and calls, CLI parity and process restart. Fresh Codex CLI sessions
exercise the installed plugin from unrelated mathematical workspaces. The
living plan records these results and the separately deferred browser/cloud
and public-distribution work.
