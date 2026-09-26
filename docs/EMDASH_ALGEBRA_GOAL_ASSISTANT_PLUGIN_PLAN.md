# Emdash Algebra Goal Assistant: Codex Plugin Plan

Date: 2026-09-25
Plan-ID: `EMDASH-ALGEBRA-GOAL-ASSISTANT-PLUGIN`
Status: review complete; GAP-1 through GAP-3 recommended for first implementation
Baseline: `37ce19d5` (completed package consumer, now integrated into main)
Branch: `goal/algebra-goal-assistant-plugin-v3.2`
Worktree: `/home/user1/emdash1-goal-assistant-plugin`

## Selected work and authority

The user selected main integration, a careful review of a Codex plugin for
Emdash, and documentation of its computational-and-internal goal-assistant
orientation. The [orientation](EMDASH_ALGEBRA_GOAL_ASSISTANT_ORIENTATION.md)
owns that product emphasis. This living plan owns the plugin design, proposed
implementation slices, qualification and recovery. The current persistent goal
covers the review and concrete plan; it does not claim that a plugin is already
built, installed or published.

Main was fast-forwarded cleanly from `40cfad99` to `37ce19d5`. All 65 then-existing
worktrees were clean. This new dedicated worktree is a descendant, bootstrapped
with pinned pnpm and its own dependency links; workspace verification passes.
The standing authorization covers local branches/worktrees and checkpoints.
There is no selected npm/plugin publication, cloud deployment, cross-repository
edit, user plugin installation, history rewrite or worktree removal in this
review. Full TypeScript and repository-wide aggregates remain waived.

The [handoff](TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md), active mathematical owners
and nested SOP still govern semantics. This work does not reopen Op/variance,
profile integration, six-term comparison, spectral research, bulk transfer or
the parked proof-agent benchmark. A plugin is a delivery and workflow layer.

## Recommendation

Build **Emdash**, an algebra goal assistant delivered first to a user's local
Codex app/CLI environment. Use Arrowgram's ordinary-file/portable-command
pattern and GetPaidX's shared-tool/transport pattern. Keep Emdash's computational
and internal mathematical libraries as the semantic owners. Codex supplies
the conversational agent; a GetPaidX account or hosted workspace is optional.

The first implementation should include a useful mathematical workflow and a
portable runtime, not stop at a manifest and a skill that names unavailable
commands. A computation-only workflow should be usable without any proof goal.
A subsequent internal-construction consumer is part of demonstrating the
intended mathematical experience, rather than treating the product as only a
calculator or a verifier.

## Reference architectures actually inspected

| Reference | Observed mechanism | Lesson for Emdash |
| --- | --- | --- |
| Arrowgram plugin | Compatibility manifest plus authoring skill; ordinary workspace files; pinned `@hotdocx/arrowgram-agent@0.1.6`; repo helper explicitly limited to development | The installed plugin must work in an unrelated user directory; canonical files and a portable command matter more than an editor session |
| Arrowgram agent package | Separate package with a CLI, workspace operations, validation, preview, builds and a whole-artifact editor bridge | Keep the pure library separate from Node/filesystem/UI hosting; derive views from the same editable source |
| GetPaidX plugin | Skill plus one remote `getpaidx-cloud` MCP configuration; OAuth endpoint at `/api/mcp` | Remote service access is a transport choice, not the definition of a Codex plugin |
| GetPaidX WebMCP | Browser MCP client lists the actual server tools, projects them through `registerTool`, and forwards execution through MCP `tools/call` | Reuse discovery, schemas and handlers; avoid a second hand-maintained WebMCP catalog |
| GetPaidX browser transport | Same MCP server factory behind `/api/webmcp/mcp`, with exact-origin browser-session authentication; hosted `/api/mcp` retains OAuth | Shared tools do not mean shared credentials, execution location or browser permissions |

Local source evidence, read-only and optional on other development hosts:

- Arrowgram checkout `/home/user1/arrowgram`, HEAD `214ec0a`: `plugins/arrowgram/`,
  `plugins/getpaidx/`, `.agents/plugins/marketplace.json`, and `packages/agent/`.
  Unrelated existing landing-page work was present; the inspected plugin paths
  were not changed by this task.
- GetPaidX implementation `/home/user1/closerfans`, HEAD `a03c667a`:
  `src/components/webmcp/getpaidx-webmcp-bridge.tsx`,
  `src/lib/webmcp/mcp-tool-projection.ts`, `src/app/api/webmcp/mcp/route.ts`,
  `src/app/api/mcp/route.ts`, `scripts/mcp/getpaidx-mcp-server.ts`, and
  `src/lib/programmatic-api/getpaidx-webmcp-contract.test.ts`.
  The inspected transport paths had no local diff. The contract test compares
  actual MCP discovery with browser registrations. It was read, not rerun.

The browser bridge feature-detects `document.modelContext`, with a legacy
fallback. It forwards cancellation and refreshes the ordinary UI after a
successful mutation. It preserves structured results even where an inline
MCP Apps resource is not rendered. WebMCP and an MCP Apps embedded view are
different mechanisms; neither requires another Emdash chat panel.

## Codex and browser platform boundary

Current official documentation supports skills and optional MCP configuration
in plugin bundles. It now recommends portable root `plugin.json`; the installed
plugin-creator skill and existing reference plugins use the still-supported
`.codex-plugin/plugin.json` compatibility layout. Use one deliberate manifest
route, validate it with the available tooling, and test the installed copy.
The local reviewed CLI is `codex-cli 0.156.1`; its help exposes plugin
add/list/marketplace commands. This review did not install or update anything.
[Plugin packaging](https://developers.openai.com/plugins/build/plugins).

Codex supports command-launched STDIO MCP and Streamable HTTP MCP. A local
plugin can therefore operate on the end user's computer without GetPaidX.
Execution is local to the selected Codex execution environment: a remote
container or development host is not automatically the user's laptop. Hosted
ChatGPT web does not read local Codex configuration; that is a separate delivery
target. [Codex MCP documentation](https://learn.chatgpt.com/docs/extend/mcp).
The mathematical runtime's location is independent of which model service the
Codex client uses; local computation does not imply a locally running model.

WebMCP registers tools in an active web document and carries its browser/origin
context. Current Chrome documentation uses `document.modelContext.registerTool`
and describes evolving lifecycle/cancellation behavior. Feature detection and
an actual supported-host test are required; a mock registration test alone does
not establish browser-agent availability.
[WebMCP imperative API](https://developer.chrome.com/docs/ai/webmcp/imperative-api).

Local plugin discovery, local installation, registry publication and public
directory submission are distinct milestones. A skill's ability to execute a
local command also does not mean all web or managed clients can execute it.
Record the tested host/version and retain an ordinary-file/CLI path.

## Proposed architecture

```text
User's mathematical goal
        |
        v
Codex + Emdash skill (interpret, plan, edit, explain, resume)
        |
        +---- ordinary workspace files / portable CLI ----+
        |                                                |
        +---- local STDIO MCP ----------------------------+
                                                         v
                                         Shared Emdash command service
                                         schemas, discovery, source identity
                                                         |
                                  +----------------------+-------------------+
                                  v                      v                   v
                          Existing CAS owners    Internal/Core owners   Derived views
                          values/maps/results    typed constructions    Vega/Arrowgram

Optional browser workspace -> WebMCP -> same MCP tools/list and tools/call
Optional remote workspace  -> HTTP MCP -> same service, host-specific execution
```

The domain service is transport-independent. Its operation implementations
delegate to existing mathematical owners. The CLI calls that service directly;
MCP exposes its bounded catalog. A browser attached to that MCP service should
project actual discovery/calls, following the inspected GetPaidX pattern.
Do not copy private SaaS implementation or introduce duplicate mathematical
handlers, a tool per Core constructor, or a separate browser catalog.

The local browser path needs an explicit bridge: page JavaScript cannot call
a STDIO process directly. A loopback Streamable HTTP adapter can expose the
same MCP factory with an explicit workspace and origin/session binding. A
hosted browser uses its host's authenticated same-origin route instead. Neither
adapter should make ambient filesystem or process access part of the pure
mathematical API.

A browser-only computational consumer can use the same pure mathematical APIs
without filesystem/process capabilities. It must report that smaller host
capability set explicitly. A long-lived MCP process is compatible with file-
based, freshly reconstructed mathematical state; it need not become a resident
proof session or the canonical source of a development.

Proposed plugin identifier: `emdash`; presentation: **Emdash — Algebra Goal
Assistant**. Proposed source is `plugins/emdash/` in this repository, with a
repository marketplace at `.agents/plugins/marketplace.json`, distinct from the
Arrowgram/GetPaidX `hotdocx` marketplace. These paths are a concrete proposal
for the next scope selection, not files created or user configuration changed
by this review. Prefer the available plugin-creator compatibility scaffold for
the first local test; portable-manifest migration can follow a demonstrated
distribution need.

## Existing Emdash assets and gaps

| Owner | Reuse | Remaining plugin work |
| --- | --- | --- |
| [Public package](../packages/emdash/package.json) and [algebra entry](../src/v3_2/package_algebra.ts) | Browser-safe computational API and Core/authoring/workspace entries | New `/algebra` exists in qualified local artifacts, not the old published npm `0.3.0`; the package has no command `bin` |
| [Repository command](../scripts/emdash) | Capability, proof, workspace and development command seams | It uses repository examples and `ts-node/register`; it is not a portable end-user executable |
| [AI-native capabilities](../src/v3_2/ai_native_capabilities.ts) | Exact implemented profiles and limitations | Its existing record primarily describes proof/workspace capabilities; add a selected plugin command catalog without rebranding all CAS results as checked Core |
| [CAS operation contracts](../src/v3_2/algebra_engine.ts) and [graphs](../src/v3_2/algebra_graph.ts) | Typed operations, exact parents, runtime validation and retained computation topology | Adapt the selected operations to portable requests/results; no new algebra engine or general scheduler |
| [External module reuse](../src/v3_2/algebra_external_module_reuse.ts) | Actual returned coefficients, typed matrices, whole complex and further internal action | Package the bounded construction path deliberately; preserve its explicit interpretation/assumption and opaque-reduction limits |
| [Development CLI](../src/v3_2/lf_proof_development_cli.ts) | Stateless reconstruction and compact JSONL/text results | Preserve existing proof protocols while presenting broader user goals through the plugin |
| [Research goal graph](../src/v3_2/research_goal_graph.ts) | Theorem/task/decision dependencies with derived evidence-sensitive status | It currently recognizes checked-proof, human-approval and AI-proposal evidence; arbitrary computed-result completion is not already implemented |
| [Vega consumer](../packages/emdash/fixtures/polynomial-vega/README.md) | A real clean package consumer, source-derived views and stale-render handling | Integrate artifact/view handoff; it is not yet a generic Emdash workspace or plugin |

The research-goal graph is optional for simple calculations. Its task nodes
support prerequisite aggregation or named approvals; there is no computation-
evidence kind. Do not force every calculation through an approval policy,
invent a checked proof, or add a generic mutable `done` field. Reuse the graph
when its model fits; review a new computational-evidence policy only for a
selected consumer that actually needs it.

## Mathematical workspace and user interaction

The user should be able to say: “Work over Q[x,y], compute this relation,
show the curves, then use the relation in a module construction.” Codex should
retain readable source and reusable results, expose meaningful assumptions and
handle repeated identifiers, encodings, hashes and artifact bookkeeping.

Use ordinary TypeScript authoring for the mathematical program, and existing
canonical data encodings for requests and derived artifacts. A small workspace
manifest can name the selected files/profiles and output locations; freeze its
minimum shape against the first consumer instead of designing a universal
notebook or goal ontology. Notes can state research goals in ordinary Markdown.
Mathematical structures and laws remain at their existing owners.

Keep ordinary host-code execution explicit. Codex can edit and run an authored
TypeScript program through its normal authorized execution host. Inspecting
inert workspace data must not secretly execute arbitrary modules, and a remote
MCP request must not acquire a generic `eval` or shell operation merely to make
authoring convenient. The existing deferred source-loader boundary is not
silently promoted by packaging a plugin.

Illustrative command/tool responsibilities, names not yet frozen:

| Responsibility | User value |
| --- | --- |
| Discover/inspect | Report available mathematical operations, objects, domains, dependencies and unsupported prerequisites |
| Compute | Return actual exact values, relations, maps or presentations with source-bound reusable artifacts |
| Construct/reuse | Build a selected whole internal object and consume it in a further operation |
| Explain/render | Produce concise mathematical explanations and views derived from retained data |
| Update/resume | Apply scoped source changes, reject stale results and resume from files across sessions |

Return compact mathematical summaries plus artifact references. Keep exact
data available on demand. Display assumptions or interpretation limits where
they affect the conclusion; do not turn every operation into a certification
or approval ceremony. An adopted equation still needs the existing explicit
caller decision and recorded status; it is not silently promoted to a proof.

## Delivery and implementation order

The initial developer prototype may bundle a reproducibly built runtime with
the plugin, using a pinned local Emdash artifact. A separately distributable
`@hotdocx/emdash-agent` is a reasonable later package, following Arrowgram, but
that name/package is only a proposal. Do not advertise an unversioned `npx`
command or depend on developer checkout paths. Keep Node/MCP dependencies out
of the browser-safe `@hotdocx/emdash` entries.

| Row | State | Concrete acceptance |
| --- | --- | --- |
| GAP-0. Review and orientation | Complete | Main integrated at `37ce19d5`; reference/plugin/MCP/WebMCP sources and official guidance inspected; orientation, implementation proposal and linked plans synchronized; document checks and exact diff review pass |
| GAP-1. Portable runtime and workspace slice | Proposed | A clean unrelated directory uses the built runtime to inspect/compute/render one source-owned algebra workflow; no developer path, global install assumption or cloud account |
| GAP-2. Local Codex plugin | Proposed | Validated manifest/skill and thin local MCP adapter over the same service; actual fresh Codex session discovers and uses the installed/cached copy on a user workspace |
| GAP-3. Internal construction and reuse | Proposed | A relation becomes typed internal module data, a whole constructed complex and a further action through existing owners; any computed-equation adoption stays explicit; restart/edit invalidation works |
| GAP-4. Browser projection | Proposed follow-up | A real supported browser registers the MCP-discovered tools and forwards calls through the shared service; ordinary UI remains usable without WebMCP; stale/cancelled results cannot overwrite newer source |
| GAP-5. Hosted distribution and richer mathematics | Deferred | Separate GetPaidX/remote host adapter, public releases, further coefficient interpretations/backends and richer mathematical consumers only when selected |

The recommended first implementation objective is **GAP-1 through GAP-3**.
GAP-1/2 provide the first usable plugin; GAP-3 checks that the product advances
the computational-and-internal objective. GAP-4 can follow without changing
the mathematical service or inventing another tool inventory. The initial
runtime should default to portable native computation; Singular is an optional
explicitly available backend. The internal-reuse adapter must accept correctly
classified retained results without disguising native output as an external
engine result. Keep the existing integer-only formal interpretation boundary
visible when the native rational computation supports more inputs.

At implementation freeze, decide only the concrete prerequisites: plugin
source/marketplace destination, bundled-runtime artifact layout, the first
workspace file contract and supported host versions. Prefer a repository-owned
source bundle with isolated installation acceptance; install into the real
user's plugin configuration only when that installation is selected. Reuse the
plugin-creator validation/update helpers and test a fresh session after changes.

## Proportional validation

Review changes: exact diff, Markdown/local-link hygiene and source attribution.
The bootstrap's workspace check is setup evidence, not new mathematical or
plugin qualification. No installed plugin, live hosted API, cloud workspace or
browser WebMCP invocation is claimed by this review.

Review qualification: document hygiene passes with 121 local links in the
changed Markdown. The checkpoint contains only eight Markdown documents:
this plan, the orientation, README, handoff, workbench ledger, and the existing
CAS, AI-native workspace and proof/goal plans. No source, package manifest,
lockfile, formal owner, plugin bundle or user configuration changed. Existing
Arrowgram/GetPaidX work was preserved. Implementation rows remain proposed.

Implementation gates should include:

- Focused runtime, schema, exact-domain and stale-source controls; opaque or
  assumed internal data retains the correct status. Existing qualified owners
  and conformance controls are reused where the selected bridge depends on them.
- Clean artifact/cache installation outside the checkout, explicit dependency
  versions and no hidden repository path or mutable `node_modules` sharing.
- Actual CLI and Codex-session end-user scenarios: compute, change input,
  reuse a result, inspect a view and resume. Success is useful mathematics and
  reduced bookkeeping, not only manifest validation or a proof benchmark score.
- Shared CLI/MCP result parity, tool inventory/schema tests and host-capability
  failures. Browser projection additionally needs actual supported-host
  discovery/execution, ordinary-UI fallback and source/revision controls.
- The applicable focused typecheck/lint/package/document gates. Keep the user's
  aggregate waiver explicit; any future release retains separate qualification.

Do not add another model API merely to test the plugin; Codex is the agent
host. No new OpenAI key, publishing credential, GetPaidX login or server is
required to produce this local design and first local runtime.

## Persistent-goal prompts

Completed review goal: complete GAP-0 under this evolving plan and the product
orientation; inspect current owners and reference implementations, record
platform qualifications, update relevant documentation and checkpoint the
review. Keep implementation rows proposed; do not claim plugin installation
or usability from the review alone.

Proposed implementation objective after scope selection: implement GAP-1 through
GAP-3 in this living plan from the current descendant state of
`goal/algebra-goal-assistant-plugin-v3.2` in
`/home/user1/emdash1-goal-assistant-plugin`. Let the plan own concrete contracts,
ordering, decisions, validation and recovery. Deliver a portable, usable Codex
algebra goal assistant over existing computation and internal-construction
owners. Preserve optional certification, exact mathematical status, source
identity, current formal qualifications and the aggregate waiver. Make validated
local checkpoints. Do not infer publication, deployment, cross-repository edits,
history rewriting or cleanup from this goal.
