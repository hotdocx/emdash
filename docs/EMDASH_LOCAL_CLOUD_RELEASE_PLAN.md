# Emdash Local And Cloud Release

Date: 2026-09-29
Status: active release preflight

This is the release continuation of the completed
[implementation plan](EMDASH_LOCAL_CLOUD_WORKSPACE_IMPLEMENTATION_PLAN.md).
The user's September 28 follow-up explicitly authorizes integration, pushes,
publication and deployment as needed, following each repository's SOP, and
requests an OpenAI submission handoff in Downloads. It supersedes the earlier
local-only authorization boundary. Prefer local Docker builds. Preserve
unrelated work in all canonical checkouts and never rewrite existing history.

## Release owners and gates

| Step | Owner and acceptance | Status |
| --- | --- | --- |
| R1 | Review refs, deployment config, dependency audits, schema diff and rollback identities | Complete |
| R2 | GetPaidX targeted dependency fixes, generated submission metadata, full isolated regression, clean release checkpoint | Complete at `a0852877`; build-network correction `dff2dbea` |
| R3 | Local gateway and three controller-family builds; reviewed additive schema, pool/job mapping and healthy gateway rollout | Additive schema applied; local image builds active |
| R4 | Hosted OAuth catalog, immediate task, direct scientific program, preview, retained artifacts and export smoke; exact fixture cleanup | Pending |
| R5 | Integrate and push Emdash; publish a new npm version with the existing exact-artifact provenance workflow | Complete: 0.4.0, tag/source `618fdb2e`; public registry artifact verified |
| R6 | Integrate and push private Arrowgram source; dry-run then publish allowlisted OSS mirror; validate plugin packages | Complete: private `5ffaddf4`, public `990bffbf`; both CI runs pass |
| R7 | Prepare versioned portal JSON/skill ZIPs, source packages, worksheet, demo script, screenshots, checksums and release evidence | Prepared in Downloads; awaiting final hosted evidence/checksums |
| R8 | Synchronize SOPs/ledgers and report published identities and remaining portal-only actions | Pending |

The existing local evidence is carried forward for unchanged code: Emdash
481 suites / 2,971 tests (2,883 pass, 88 existing skips), GetPaidX 381 suites /
1,571 pass / 2 skips, controller 98 pass / 1 existing skip, actual configured
Codex and program executions, browser interaction, and network-disabled exact
export replay. Dependency changes require renewed affected GetPaidX gates.
Package publication requires its owning packed-install and release checks.
This release does not promote any new mathematical qualification.

## Initial review

- Emdash implementation head: `3142fa4b`; canonical main `4b7469e2`, 86 commits
  ahead of unchanged public main. The history includes the recorded qualified
  action-profile integration, DevOps and algebra/plugin work. Publish their
  descendant rather than removing or rewriting these integrated checkpoints.
- GetPaidX implementation head: `217cc3a7`; canonical master `a03c667a` has an
  unrelated CRM report edit. This repository has no Git remote configured.
- Arrowgram implementation head: `6597cb4`; canonical main `214ec0a` has
  unrelated consulting-site edits. Use a clean main checkout for the guarded
  OSS export; do not export the private LastRevision SaaS or private history.
- npm currently serves `@hotdocx/emdash` 0.3.0, without the newer `/algebra`
  entry. Plan an additive 0.4.0 release, retaining existing profile boundaries.
- Gateway audit finds vulnerable `fast-uri` and `ip-address` transitives.
  Resolve through compatible targeted updates, then require zero full and
  production findings including the clean/pruned Docker dependency graph.
- Full release is required because controller protocol and Prisma schema
  changed. Inspect the live schema before allowing the deploy script's schema
  synchronization. Preserve runtime secrets and existing live sessions.

## Submission boundary

Prepare the canonical GetPaidX listing update against the deployed 62-tool
surface, separately label Codex plugin source archives and Emdash companion
skills, and do not claim OpenAI directory approval. The user will upload the
requested files. Never include credentials in JSON, ZIPs, screenshots or Git.
Retain the already-published listing until the portal review completes.

## Release evidence in progress

The regenerated GetPaidX submission has 62 explicit three-hint annotations and
62 output schemas, five positive and three negative tests. The tests now cover
direct scientific programs and immediate tasks. Recommended portal version is
1.2.0 under the existing listing, with the GetPaidX and Emdash cloud skills.
The optional separately branded cloud skill is packaged honestly as a
skills-only companion requiring the existing connection. The local STDIO
plugin ZIP includes its runtime but is not labelled as a hosted MCP upload.
The [current official submission requirements](https://developers.openai.com/plugins/deploy/submission)
require HTTPS for normal remote-MCP submissions and direct local-MCP questions
to an OpenAI contact; no duplicate OAuth endpoint is introduced to evade this.

GetPaidX's fresh root tests pass 381 suites / 1,571 tests / two existing skips.
Its controller has 98 passing tests / one existing skip; OAuth's six focused
tests also pass. Full and production audits for both graphs are clean after
three targeted dependency fixes. Emdash packed-install/release tests, copied
local CLI/SDK tests and plugin validation pass. Its fresh complete TypeScript
gate passes at the versioned package boundary: 481 suites, 2,971 tests,
2,883 pass, 88 existing skips and zero failures in 2,515.9 seconds. This
includes workspace/typecheck/lint and the complete root test aggregate.

The tooling gate exposed an existing process-reaping race in the test of the
systemd resource guard. The test now accepts both Linux process-disappearance
errors during its `/proc` read, while still rejecting a live descendant. No
resource guard or mathematical owner changed. The full tooling gate passes,
including registry, health-inventory and generated-catalog checks.

Arrowgram's documented shell helpers lacked executable Git modes. Correcting
the two OSS export/sync modes made the documented guarded flow work from a
clean clone. Private `5ffaddf4` passed CI run `36518706094`; public `990bffbf`
passed CI run `36519285052`. The reviewed public diff contains the two plugin
updates and the SOP-required regenerated public-only lockfile (compatible
resolutions); it contains no private SaaS workspace or private history.

Two local gateway builds reproduced registry timeouts from Node network-family
autoselection. An isolated Node 22/npm 10 audit passed with the host's existing
IPv4-first/no-autoselection settings; the builder now carries these flags only
in its build stage. Audits remain mandatory and production Node settings stay
unchanged. No ACR build was used. The live gateway remains revision `0000167`
until the guarded release applies its exact image manifest.

Operator bundle: `/home/user1/Downloads/emdash-getpaidx-release-20260929`.
The final release evidence and integrity manifest will be written after hosted
acceptance; preparatory artifacts are not yet claims of deployed success.

## Published package and local installation

Emdash main was fast-forwarded and pushed at `618fdb2e`; annotated release
`emdash-v0.4.0` points to that immutable source. npm workflow `36521885693`
built and published successfully through the existing trusted-publisher route
after the user-authorized environment approval. npm reports 0.4.0 and its SLSA
provenance attestation. The registry tarball and the workflow's exact artifact
have identical SHA-256
`999649a3f0869e8322e4a99adfd7da7d3473cbcfdcc826805b4e13e8ca4b9f58`.
The registry-downloaded tarball passes the independent packed consumer checks,
including ESM/CJS algebra, declarations and browser bundling.

The [GitHub release](https://github.com/hotdocx/emdash/releases/tag/emdash-v0.4.0)
provides the prebuilt local/cloud marketplace, cloud skill, portable scientific
workspace and exact npm tarball. The user's `personal` marketplace now points
at canonical `/home/user1/emdash1`, replacing the old implementation-worktree
source. Local `emdash` and `emdash-cloud` are installed at
`0.1.0+codex.20260929035421`; source/cache comparisons pass. A new Codex thread
is needed to pick up the updated installed skills/tools.

The first public aggregate found an older documentation link to an optional
host-local Cisinski text. Commit `8c7cd1bc` replaces only that link with the
portable local-resource index; mathematical claims and evidence are unchanged.
The full changed-document gate passes locally, and public aggregate
`36522289039` is validating that corrected main. The package's independently
qualified release artifact remains pinned to `618fdb2e`.

The user clarified that GetPaidX should normally use simple sequential work in
its canonical checkout. Its worktree SOP now describes this release as an
optional exception for clean staging beside unrelated edits, not a requirement
for parallel development or multiple Docker stacks. The user then explicitly
asked to checkpoint the leftover CRM report. It is preserved in a separate
canonical commit `4256e2e6`; GetPaidX master and the release worktree are clean.
That report checkpoint performs no CRM campaign or implementation action.
