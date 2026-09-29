# Emdash Cloud Profile

A skills-only companion to the existing GetPaidX/LastRevision tool connection.
It uses generic workspace programs for calculations and immediate Codex tasks
for delegated agent work. It includes neither an MCP server nor another OAuth
client, and it does not require Node on the user's computer.

The implementation is qualified locally and its coordinated hosted release is
recorded in the [release plan](../../docs/EMDASH_LOCAL_CLOUD_RELEASE_PLAN.md).
The live GetPaidX connection must expose `run_workspace_program` before use.
The existing `emdash` plugin remains independently usable for local work.

The `emdash_scientific` template is built from the portable source project:

```bash
node packages/emdash/scripts/build-scientific-workspace.mjs --out /absolute/empty/artifact-directory
node packages/emdash/scripts/verify-scientific-workspace.mjs
```

The default template pin is Node 22.23.2, the qualified controller version.
Use the actual workspace runtime when selecting a pin. Library source and
bundle hashes are recorded under `vendor/build.json`. The portable workspace
includes its exact runtime; npm installation is unnecessary for this template.

Local and cloud skills package the same mathematical guidance from
`docs/EMDASH_PLUGIN_MATHEMATICAL_GUIDANCE.md` using
`packages/emdash/scripts/sync-plugin-guidance.mjs`. Do not edit the copies.
