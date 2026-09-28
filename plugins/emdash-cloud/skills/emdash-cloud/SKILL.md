---
name: emdash-cloud
description: Compute, explore and reuse Emdash mathematics in a selected GetPaidX or LastRevision cloud workspace through its existing authenticated tools.
---

# Emdash In A Cloud Workspace

Use this profile for a selected cloud workspace. It supplies mathematical
guidance; GetPaidX supplies execution, storage and authentication. It needs no
local Node server or separate OAuth client. Local mathematics belongs to the
independent `emdash` profile. Report which project/workspace you are using;
do not silently change targets.

## Establish The Available Cloud Workflow

Use the existing authenticated GetPaidX tool connection. Inspect its live
catalog for `run_workspace_program` and `run_workspace_codex_task`. These
features require the new workspace-execution runtime; an older hosted
connection may not have them. Explain an unavailable capability accurately
instead of claiming a program ran or quietly turning it into a delegated task.

Reuse the user's selected active read-write session. For a requested new
scientific example, inspect the live templates for `emdash_scientific` and
start that workspace through the normal GetPaidX flow. Do not replace an
existing project with a demonstration. The template carries a pinned portable
Emdash library and its declarations; do not assume an older npm package has
the same exports.

## Author And Run Mathematics

Inspect `workspace.program.json` with `getpaidx_inspect_workspace_program`.
The pilot's `compute` task composes exact membership, native complex reuse and
a plot; `reuse` checks the supplied `retained.json` without replacing its
coefficient choice. Read the project README and declarations for authoring.

Use `getpaidx_read_workspace_file` and `getpaidx_write_workspace_file` to edit
`input.json` or the TypeScript program. Carry expected hashes and runtime pins
yourself; ask the user about mathematical choices, not opaque identifiers.
Inspect again after an edit, then call `getpaidx_run_workspace_program` with
the returned revision, selected task, parameters and a stable idempotency key.
One program may call many library functions. A new mathematical operation does
not require another platform tool.

Poll with `getpaidx_get_workspace_execution` until terminal. Retain the same
key/input after an uncertain start. A `sourceChanged` result describes the
captured input, while the current project has moved on. Retrieve compact
artifacts with `getpaidx_read_workspace_execution_file` and show the scientific
preview when available. Exact coefficients remain strings.

Use the immediate Codex-task tool when the user wants delegated authoring,
setup or other agent work inside the workspace. Ordinary authored calculations
use the direct program tool. Scheduled/event-driven work retains GetPaidX's
automation workflow. Cancel through the shared execution tool when requested,
then inspect the terminal outcome.

## Interpret And Continue A Result

Read [the shared mathematical contract](references/mathematical-contract.md)
before interpreting a retained complex or internal proof result. Native reuse
needs no adopted equation. Optional internal mode requires explicit
`internal: true` and an `adoptionReason`; preserve the current one-assumption
Core boundary and distinguish it from a closed proof.

For a later `reuse` run, copy its retained artifact into the project's
`retained.json` with the normal expected-hash update. A stale or invalid
relation must fail visibly. For export, start with the completed execution's
`metadata/request.json`, then retrieve its declared `source` and `artifacts`
files. Follow byte cursors and encoding fields. Export the captured input,
parameters and library pins; current mutable source may describe another run.
Conversation and browser state reference that durable project.
