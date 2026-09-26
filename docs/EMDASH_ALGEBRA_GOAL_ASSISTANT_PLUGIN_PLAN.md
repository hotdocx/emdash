# Emdash Algebra Goal Assistant: Codex Plugin Plan

Date: 2026-09-25
Plan-ID: `EMDASH-ALGEBRA-GOAL-ASSISTANT-PLUGIN`
Status: GAP-1 through GAP-3 selected and active; cloud transport comparison recorded
Baseline: `37ce19d5` (completed package consumer, now integrated into main)
Implementation continuation baseline: `06769acc`
Branch: `goal/algebra-goal-assistant-plugin-v3.2`
Worktree: `/home/user1/emdash1-goal-assistant-plugin`

## Selected work and authority

The user selected main integration, a careful review of a Codex plugin for
Emdash, and documentation of its computational-and-internal goal-assistant
orientation. The [orientation](EMDASH_ALGEBRA_GOAL_ASSISTANT_ORIENTATION.md)
owns that product emphasis. This living plan owns the plugin design, proposed
implementation slices, qualification and recovery. The current persistent goal
now covers implementation through GAP-3 following the user's acceptance of
review checkpoint `06769acc`. The earlier review is complete. The user also
selected a feasibility comparison for cloud-container tools reachable from
desktop Codex; that comparison does not select a cloud deployment.

Main was fast-forwarded cleanly from `40cfad99` to `37ce19d5`. All 65 then-existing
worktrees were clean. This new dedicated worktree is a descendant, bootstrapped
with pinned pnpm and its own dependency links; workspace verification passes.
The standing authorization covers local branches/worktrees and checkpoints.
The accepted implementation includes the proposed repository plugin/marketplace
and local installed-copy acceptance. There is no selected npm/public-directory
publication, cloud deployment, cross-repository edit, new main integration,
history rewrite or worktree removal. Full TypeScript and repository-wide
aggregates remain waived.

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

## Cloud container tools for desktop Codex

The user's proposed future mode is architecturally feasible: Emdash's runtime,
dependencies and mathematical workspace can live in a GetPaidX container while
desktop Codex remains the user's agent interface. Starting a STDIO server in
that container alone does not create a remotely reachable endpoint. STDIO is
a process pipe; a network transport or an execution/relay integration must
connect the desktop client to it. Streamable HTTP supplies a distinct network
transport. [MCP transports](https://modelcontextprotocol.io/specification/2026-07-28/basic/transports).

| Design | What is on the end-user host? | Connection and tradeoff |
| --- | --- | --- |
| Local Emdash runtime, selected first | Codex plus the plugin runtime and its host prerequisites | Direct local STDIO; least platform coupling and useful without an active cloud workspace |
| Cloud Codex uses container-local Emdash STDIO | Codex/GetPaidX client; no local Emdash mathematics installation | The user delegates work to the workspace agent through existing workspace workflows; Emdash tools belong to the cloud agent, so this is agent delegation rather than direct desktop Emdash tools |
| Desktop Codex calls workspace HTTP MCP | Codex plus a remote plugin configuration; no local Emdash runtime | A stable authenticated gateway routes to a workspace-bound Emdash service; best direct-tool product path for ordinary hosted containers, but needs lifecycle, routing and actor/workspace authorization |
| Desktop STDIO command relays to the container | A small authenticated relay/remote-execution client; no local Emdash mathematics installation | Preserve STDIO JSON-RPC end to end over a supported channel; useful on developer hosts, but requires robust process/session teardown and does not arise from merely starting a container process |
| Existing GetPaidX MCP brokers mathematical operations | GetPaidX connection and workflow skill; no local Emdash runtime | Reuse existing access/workspace selection and call the Emdash service behind it; avoids another client connection but needs a maintained schema/version/discovery adapter |

For a generic remote development host, an SSH-launched remote STDIO process is
a possible relay arrangement. It is not evidence that GetPaidX exposes SSH or
raw controller access to end users. A GetPaidX implementation should use an
authorized platform gateway/relay, preserving its workspace policy. The MCP
server's stdout must remain protocol-only; logs use stderr, and disconnects
must retire the correct child process/session.

Codex documents `experimental_environment = "remote"` for STDIO when a remote
executor environment is already available. That setting does not by itself
enroll arbitrary GetPaidX containers as Codex remote executors.
[Codex MCP configuration](https://learn.chatgpt.com/docs/extend/mcp).

Recommended future sequence: first use the same portable local runtime inside
a cloud workspace for its in-container Codex. If users need direct desktop
tool calls, add a workspace-bound HTTP MCP adapter or a broker behind the
existing GetPaidX endpoint. An internal HTTP-to-STDIO proxy may bridge the
same factory without duplicating mathematical handlers. Bind requests to the
authenticated actor, selected workspace/session, supported runtime version and
source revision; gateway-owned paths must not come from arbitrary client file
paths. Persist mathematics in the workspace files, not the transport session.

An open workspace session is a natural initial lifetime for that service.
Closing/suspending the workspace should produce an unavailable/disconnected
result; reopening should reconstruct from files and reject obsolete handles.
Cold-start readiness, cancellation, concurrency, access revocation and artifact
handoff need explicit acceptance before claiming this mode works. WebMCP can
project the resulting MCP inventory inside an authenticated browser workspace;
it does not supply desktop-to-container connectivity by itself.

This is a documented feasibility/design assessment, not an implemented GetPaidX
feature or a tested cloud route. GAP-5 remains deferred, and no cloud API,
controller, credential, public endpoint or workspace session was modified.

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
| GAP-1. Portable runtime and workspace slice | Complete at focused qualification | Copied standalone runtime passes CLI/fresh-process/typed-authoring acceptance outside the checkout; exact source, retained computation, update and derived view controls pass |
| GAP-2. Local Codex plugin | Complete at focused qualification | Validated source/cache, real SDK STDIO and CLI parity, and actual fresh Codex CLI calls from an unrelated workspace pass |
| GAP-3. Internal construction and reuse | In progress | A relation becomes typed internal module data, a whole constructed complex and a further action through existing owners; any computed-equation adoption stays explicit; restart/edit invalidation works |
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

## Implementation decisions and recovery

- Continue on the existing dedicated branch from `06769acc`. The inventory has
  67 worktrees; an unrelated action-profile integration worktree has a plan edit.
  Preserve it. This plugin worktree's staged/unstaged state was clean.
- Baseline: workspace verification and root typecheck pass. The public algebra
  and external-module-reuse suites pass eight tests with one unchanged live
  Singular/Lambdapi opt-in skip (nine total, 4.95 seconds). No aggregate ran.
- Keep one mathematical source and explicit derived artifacts in an ordinary
  workspace. The first inert source contract names rational polynomial inputs,
  ordered variables/generators and a query. Existing arithmetic/parent/schema
  owners validate them. TypeScript authoring can produce that data explicitly;
  the inspection/MCP path does not load arbitrary user modules.
- Separate pure request/source/computation helpers, Node file commands and the
  MCP adapter. Bundle a relocatable Node runtime for the plugin, with no imports
  resolved back into the contributor checkout. Keep any MCP SDK dependency out
  of the public browser-safe package entries.
- Reuse the whole-complex assembly. Extract a neutral retained-relation seam
  where needed so native results retain their real origin and the existing
  external consumer still retains actual external coefficients. Preserve all
  existing source/result binding and explicit-adoption controls.
- Current acceptance includes the generated plugin/marketplace source paths
  proposed above, local cache installation and a bounded fresh-client smoke.
  Neither these checks nor runtime discovery authorize unrelated application
  actions, cloud deployment, publication or Git changes in user math workspaces.
- Scope/cloud comparison checkpoint: `a1d43737`; implementation goal active.
- GAP-1: `algebra_goal_source.ts` defines the bounded inert rational-polynomial
  source using existing exact/parent/polynomial owners. TypeScript builders can
  emit it through the separate authoring entry. Node-owned file commands retain
  exact source revisions, preceding source bytes, computational coefficient
  data and derived view artifacts. The command catalog/dispatcher is shared
  with the forthcoming MCP adapter. No arbitrary source loader is introduced.
- GAP-1 qualification: root typecheck, changed-source lint and all 12 focused
  tests pass (2.25 seconds); 458 suites are registered. UTF-8 chunk boundaries
  and normalized-source expansion beyond the file limit have dedicated controls.
  The copied-runtime acceptance passes CLI initialize/inspect/compute/render,
  fresh-process resume, TypeScript declarations and actual native TypeScript
  authoring, revision-checked updates and stale-source rejection. It uses its
  own temporary directory and no copied/symlinked dependency graph. The runtime
  build owns generated `plugins/emdash/dist/` and hashes its source/bundle inputs.
  [Runtime guide](../plugins/emdash/README.md). No aggregate, formal-owner change
  or Lambdapi invocation was needed for this source/file slice.
- GAP-1 checkpoint: `65bad0b4`.
- GAP-2: the plugin-creator scaffold supplies the repository marketplace,
  compatibility manifest and companion MCP configuration. Its default marketplace
  name is `personal` (no existing home/personal marketplace was present). It is
  registered from this worktree, distinct from `hotdocx`; no home marketplace
  file was created. The skill gives mathematical workflows and carries revisions
  on the user's behalf. SDK `1.30.0` is pinned as a root development dependency;
  the lock delta only adds its dependency closure, leaving existing versions and
  public package entries unchanged.
- `algebra_goal_mcp.ts` derives tool names, JSON schemas and annotations from the
  shared command catalog. Fixed bundled child workers enforce a 30-second
  deadline, 512 MiB V8 heap, input/output limits and two concurrent operations.
  Cancellation/closure retires workers; source/module/shell execution is not a
  tool capability. Local tools take explicit absolute workspace roots and reject
  the installed runtime directory. A future hosted adapter must instead supply
  authorized roots from its actor/workspace context.
- GAP-2 qualification: workspace/typecheck and changed-file lint pass; all five
  MCP catalog/protocol/cancellation/worker-bound tests pass, and 459 suites are
  registered. Skill and plugin validators pass for source and installed cache.
  The copied-plugin STDIO acceptance passes actual SDK discovery/calls, CLI
  result parity, computation/rendering, process restart, revision updates and
  stale/root rejection. Generated runtime and selected source files match the
  installed `/home/user1/.codex/plugins/cache/personal/emdash/0.1.0` byte-for-byte.
- Actual Codex CLI 0.156.1 smoke: `/tmp/emdash-codex-smoke-l3grogws`, with other
  user MCP servers/plugins disabled for that invocation. The successful fresh
  session used only `emdash_inspect`, `emdash_initialize`, `emdash_compute` and
  `emdash_render`; it ran no shell commands and returned the actual `(-x,1)`
  relation and view path. Source/result/view identities and HTML hash were checked
  independently. The first launch failed before starting because CLI override
  keys were TOML-quoted; plain dotted CLI keys corrected that configuration-only
  issue. The transcript is `events-v2.jsonl`, exit zero, and stderr is empty.
  No hosted GetPaidX action or production data was involved. The app's GUI was
  not separately exercised, and no new client version was installed.

## Persistent-goal prompts

Completed review goal: complete GAP-0 under this evolving plan and the product
orientation; inspect current owners and reference implementations, record
platform qualifications, update relevant documentation and checkpoint the
review. Keep implementation rows proposed; do not claim plugin installation
or usability from the review alone.

Active implementation objective: implement GAP-1 through
GAP-3 in this living plan from the current descendant state of
`goal/algebra-goal-assistant-plugin-v3.2` in
`/home/user1/emdash1-goal-assistant-plugin`. Let the plan own concrete contracts,
ordering, decisions, validation and recovery. Deliver a portable, usable Codex
algebra goal assistant over existing computation and internal-construction
owners. Preserve optional certification, exact mathematical status, source
identity, current formal qualifications and the aggregate waiver. Make validated
local checkpoints. Do not infer publication, deployment, cross-repository edits,
history rewriting or cleanup from this goal.
