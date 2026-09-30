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
| R3 | Local gateway and three controller-family builds; reviewed additive schema, pool/job mapping and healthy gateway rollout | Complete at revision 169; qualified metering correction requires a gateway follow-up |
| R4 | Hosted OAuth catalog, immediate task, direct scientific program, preview, retained artifacts and export smoke; exact fixture cleanup | OAuth/program/task phases pass; metering fix, browser/reopen/replay and controller cleanup remain |
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

The regenerated GetPaidX submission has 62 explicit three-hint annotations,
five positive and three negative tests. Its generator independently requires
an output schema on each of the 62 MCP tool descriptors. The portal JSON
contains annotation metadata and justifications; the endpoint scan supplies
the tool schemas. The tests now cover
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

## First hosted CI follow-up

The corrected public run passed docs, package, reviewer and publication gates,
but exposed two independent infrastructure issues before the formal checks.
The progress-reporter test matched a heartbeat's last-event description as if
it were a standalone fast-test completion line. Its assertion now matches only
the actual completion-line prefix; reporter behavior is unchanged.

The pinned opam setup rejected the upstream Pratter 5.0.1 archive with a bad
checksum. The official opam cache and the existing accepted local archive both
match the original MD5 `7a75f978f8746f5745318422d562e361` and SHA-256
`1083dd78ef5413366fdd0bcfcdb19a59f92d145f677d89a502a5da109e965cac`.
The installer now seeds those exact reviewed bytes into opam's download cache,
with package-version and both digest checks. No compiler, package, Lambdapi
source or mathematical evidence pin changes. Tests cover verified-cache reuse,
changed upstream/cache rejection and refusal to override the package version.

The next hosted setup successfully installed the exact archive and checker,
then revealed that Actions forces colored opam output even when it is piped.
After removing ANSI sequences from the diagnostic, every installed package
matches the unchanged manifest and there are no unexpected dependencies.
Machine-readable package collection now explicitly passes `--color=never`.
Verification is exercised locally with `OPAMCOLOR=always` to reproduce the
hosted environment without changing any package or source pin.

## Cold formal CI resource follow-up

This concerns Emdash's repository validation, not the GetPaidX scientific
runtime: the cloud pilot executes Node/TypeScript, and the cloud LambdaPi image
retains its existing independent recipe. The pinned formal verification setup
was introduced by `f9ae8d6a` on September 23, before this cloud implementation.

After setup succeeded, the cold affine-glue library check exceeded the ordinary
2 GiB address-space limit. A source-identical temporary package, containing no
compiled objects, reproduces the allocation failure with `o=20,v=1024` in
48.230 seconds (maximum child RSS 1,818,884 KiB). Under the existing authorized
action-profile 3 GiB/90-second profile, that same owner passes in 46.310 seconds
(1,933,456 KiB), and its required `commutative_ring_affine_glue` reviewer passes
in 53.275 seconds (2,341,096 KiB). Exact receipts are
`20260929T051747Z-a9a7500a802341f1a36cbaf0920f43ba`,
`20260929T052035Z-08819d7a9b614e6e8fda2e545ee61ab3` and
`20260929T052228Z-d5482add87094e70ae544106b2ab8012`.

Only these two target bindings select the already existing
`action-profile-3g-90s` profile. Defaults, memory ceiling, checker source,
mathematical sources, subject reduction, serialization and no-swap remain
unchanged. The action-profile resource ledger records the same bounded
follow-up under the user's standing resource authorization.

## User-requested background handoff

The user requests a final response while existing background work continues,
and will resume the goal afterward. Leave the local controller build (process
1080938 at handoff, tool session 30622) and GitHub run `36526254196` running.
The local log is `/tmp/getpaidx-release-controller-retry.log`; the build helper
already pushes all three images after all three builds succeed. No extra manual
deployment wrapper is needed or retained. If a push fails after build completion,
the existing `az acr login` and `docker push` commands suffice.

Controller build source is GetPaidX `3874736d`; gateway image source remains
`dff2dbea`. GetPaidX canonical master and the release checkout are clean. The
gateway still serves revision 167; only its additive execution table has been
applied. The prepared standard-rollout manifest generator and attended hosted
acceptance script are retained under that release checkout's ignored
`reports/env/`. Resume at R3: inspect build/image results and current live work,
then use the existing repository rollout SOP and complete R4/R7/R8. Do not
infer that a finished build means production deployment or hosted acceptance.

The OpenAI bundle remains prepared at the recorded Downloads path. Final
hosted evidence, bundle checksums and portal handoff verification are still
pending. The user prefers ordinary sequential GetPaidX development; this one
existing release worktree remains a bounded staging exception.

## September 30 resumed build diagnosis

The previous background build ended at the publisher fixture's pnpm fetch,
before PDF generation, with `ERR_PNPM_META_FETCH_FAIL` and `ETIMEDOUT`.
Pinned pnpm 11.16.0 explicitly enables connection-family autoselection,
overriding Node's disabled default. A five-second per-address connection
attempt and fetch concurrency four resolve the failure with the frozen
lockfile, TLS and supply-chain checks intact. GetPaidX commit `0d311554`,
also fast-forwarded into its clean canonical master, scopes the adjustment to
that build step. The exact 89-entry policy check, offline install and PDF/qpdf
smoke pass. Expensive preceding layers are reused.

The universal candidate passes separate offline publisher, LaTeX and repeated
Paged.js book checks. The local helper continues LambdaPi and Lean, then pushes
all three images. Its new log is `/tmp/getpaidx-release-controllers-sep30.log`
(tool session 59365 at launch); this replaces the terminal retry log. Download
probes still measure roughly 14–16 KB/s from two Debian mirrors. Local builds
remain selected; no ACR build or additional deployment wrapper was introduced.
Live inspection still shows gateway revision 167 and no active workspace
sessions; recheck before applying the reviewed rollout.

Public CI `36526254196` passed TypeScript, conformance, scale conformance,
docs, tooling, package, reviewer and publication gates, but failed the formal
gate at `emdash3_2_one_cat_homology_covers.lp` (allocation failure). A cold
source-identical replay reproduces it at ordinary defaults in 24.718s. Scoped
`o=20,v=1024` passes within the same 2 GiB/90s limit in 36.062s; the native
window owner and concrete reviewer pass in 32.835s and 30.938s. No mathematical
source or profile binding has been changed at this checkpoint.

A bounded serial follow-up inventories the 16 ordinary-profile targets that
import that owner. It tests defaults, then the same 2 GiB GC control only after
an allocation failure; any other failure stops for review. Results/receipts:
`/tmp/emdash-homology-cold-followup-results.json`, log
`/tmp/emdash-homology-cold-followup.log`, launcher
`/tmp/emdash-homology-cold-followup.py` (tool session 5861 at launch). Finish
that measurement and register only qualified exact-target settings before
the next public formal run. This is separate repository CI maintenance, not
a dependency or checker requirement for the hosted TypeScript pilot.

The user requests another pause while those background processes finish.
GetPaidX runtime evidence is checkpointed at `d6b4be90`, following build fix
`0d311554`, and integrated into canonical master. Leave both existing processes
running. The image helper uploads after all three builds succeed; production
deployment is a subsequent attended step. Three `pushedDigests=` lines in its
fresh log indicate successful image uploads. The formal measurement log ends
with `Completed all 16 bounded targets.` on success, or stops at the first
unexpected failure for review. Read the results before changing profile
bindings or restarting a failed mathematical check.

If the image helper is interrupted, first confirm no copy is still running,
then resume its normal cached build/push command:

```bash
cd /home/user1/closerfans-workspace-executions-v1
az acr login --name getpaidxstagingacr
nohup env IMAGE_TAG=dev-20260929-workspace-executions-r1 \
  WORKSPACE_CONTROLLER_IMAGE_REPOSITORY=getpaidxstagingacr.azurecr.io/controller \
  CONTROLLER_BUILD_PUSH=true \
  bash scripts/build-controller-images.sh \
  > /tmp/getpaidx-release-controllers-sep30.log 2>&1 < /dev/null &
```

This starts no deployment and introduces no replacement rollout wrapper. A
successful build/push does not complete R3/R4; resume the goal to inspect the
immutable registry digests, revalidate current live state and run the standard
guarded rollout and hosted acceptance.

## September 30 image completion and refreshed preflight

The prior goal turn made concrete progress: it fixed and qualified the pnpm
failure, committed the change and resumed the builds. Both background jobs are
now terminal. All three controllers built and uploaded successfully under
`dev-20260929-workspace-executions-r1`; exact ACR digests match local images:

- universal: `sha256:2b3f8a45f270be63751792f67ab721d64c8f7d311fc7395c52f55de1cb2e3e13`;
- LambdaPi: `sha256:aed05e368146472a0727c5a5ba763ed7d5601b4197d93a80865f4576e2d580b8`;
- Lean: `sha256:272288967888ae44818e133945211aff5381825bf8c7af5583ffffd674958242`.

LambdaPi and Lean root/non-root runtime smokes pass on those exact images;
the universal image retains its prior offline books and Emdash execution
acceptance. The controller full/production audits remain at zero findings.
The refreshed gateway full and production audits expose five dependency
findings absent from the September 29 audit. Compatible targeted updates are
being qualified before a new gateway build: brace-expansion 1.1.21/2.1.7/5.0.12,
engine.io 6.6.11, fast-uri 3.1.8, ip-address 10.7.2 and markdown-it 15.0.2.
Only seven lockfile package entries and two existing override pins change.
The clean installation and updated lockfile audits report zero findings.
Full isolated regression passes 381 suites / 1,571 tests / two existing skips
in 74.469s, and fresh typecheck passes. GetPaidX commit `799f0c77` is integrated
into clean canonical master. The disposable regression database was removed
after validation. A replacement gateway build/push is running locally at
`dev-20260930-workspace-executions-r2`; log
`/tmp/getpaidx-release-gateway-r2-20260930.log`, tool session 65514 at launch.
The Docker clean/pruned audits remain required. Keep the uploaded controller
images unchanged.

The read-only deployment preflight reached a transient database-connectivity
failure; a direct retry succeeds with zero live sessions. No deployment
mutation occurred. Regenerate the manifest with the new gateway source/tag
after qualification; rebind its current fingerprints before apply.

The formal follow-up stopped exactly at its first unsuccessful 2 GiB GC
control. The reviewed continuation completes all 16 affected targets: 13 pass
at 2 GiB with scoped GC, three require the existing 3 GiB/90s profile.
Their exact bindings and receipts are recorded in the
[resource ledger](EMDASH_ACTION_PROFILE_RESOURCE_QUALIFICATION.md#september-30-cold-homology-consumer-follow-up).
No mathematical source changes. The complete tooling gate passes at receipt
`tooling-20260930T090405Z-94ccff361cfd4961a498d30266a83d30`; document checks pass.
The bounded CI repair is committed, integrated and pushed as `cfab92fc`.
Public validation run `36693986974` is queued/running for that exact commit;
inspect its formal result before claiming a green public aggregate. Keep
documentation-only follow-up checkpoints local while it runs to avoid
canceling the active validation through a superseding push.

The ignored rollout-manifest generator now selects gateway R2/source
`799f0c772bb050fb248fc2a846b17c7799a53e33`, retaining all controller R1 digests.
The existing generated R1 manifest is stale and must not be applied. Run the
generator after gateway R2's upload succeeds, then repeat the read-only
preflight and bind current gateway/job fingerprints. The production gateway
remains revision 167; all hosted acceptance and final submission evidence are
still outstanding.

## Prepared artifact integrity follow-up

The next continuation classifies the preceding turn as progress: compatible
gateway patches were qualified and committed, the replacement build was
started, and measured formal profiles were pushed. Its live build handle and
CI run remain active; package, tooling, reviewer, docs, publication and
conformance CI jobs have passed at the latest observation. Remaining jobs are
still required.

All nine ZIP files currently in the Downloads bundle pass ZIP integrity,
duplicate-name and path-traversal checks. The npm tarball has 194 members and
matches the published/workflow SHA-256 recorded above. The two cloud skill
copies are byte-identical. `npm run openai:submission:check` passes against
the actual source MCP descriptors: 62 tools, five positive and three negative
tests, all three annotations and every output schema. The Downloads JSON
matches that checked generator output byte for byte. This proves the prepared
source artifacts; the deployed scan, hosted media and final bundle integrity
manifest remain pending until rollout/acceptance.

## Revision 169 and hosted acceptance findings

Gateway R2 built/pushed successfully at
`sha256:75bcce55b6e5ba2242046119e6b7057ab1a9b732d0c789e63e8e299b7e5d9e2b`.
Its clean-install and pruned Docker audits pass. The guarded rollout reaches
healthy revision 169 with all four original schedules restored and no
unresolved cloud write. Independent SDK fingerprint comparisons verify the
expected gateway/job templates and preservation of unrelated configuration
and secret references. Canonical production env runtime keys were updated
individually with a private backup; all unrelated parsed values are preserved.
The encrypted original-state snapshot and verification receipt remain in
GetPaidX's ignored `reports/env/`.

Hosted `execution-sep30-r1` stops before a workspace start at the operator's
five-second credit transaction deadline. Independent checks confirm a disabled
identity, zero wallet balance and zero sessions. Only the operator grant and
reclaim transactions now use an explicit 30-second deadline.

Hosted `execution-sep30-r2` passes DCR/PKCE OAuth, the deployed 62-tool 0.3.0
catalog (275 endpoints/24 workflows), compute/reuse/internal runs with no model
usage, captured export, stale-source rejection, cancellation and a real
immediate Codex file change with idempotent replay. It stops at the model
usage assertion; browser/reopen phases have not run. All own sessions are
closed, post canceled, OAuth credentials revoked, unused credits reclaimed
and identity disabled. Its exact controller cleanup remains required.

Focused regressions reproduce a delayed-heartbeat loss of usage and
cross-request attribution through the shared proxy emitter. GetPaidX
`657d795b` fixes both by using a proxy per request and attaching all response
observers before starting the heartbeat write. Both tests fail on the old
implementation and pass after the fix. Full isolated regression passes
382 suites/1,573 tests/two skips; typecheck/lint and standalone scientific
template typecheck pass. Generated exports are excluded from contributor
Jest/typecheck discovery. Gateway R3 is building/pushing locally from this
clean checkpoint; log `/tmp/getpaidx-release-gateway-r3-20260930.log`, session
55676 at launch. Retain all controller R1 digests and repeat hosted token
accounting after the guarded gateway update.

Public run `36693986974` passes every non-formal job, including TypeScript,
but stops at `emdash3_2_one_cat_native_snake_inner_zeros.lp` (exit 134/23.914s).
A cold source-identical 2 GiB/90s replay with scoped `o=20,v=1024` passes in
38.464s (receipt `20260930T102429Z-97bb95aae170469092a7ef43e5043046`).
There are 25 ordinary-profile owners/reviewers importing this owner. The next
bounded follow-up measures only that group at defaults, then GC at 2 GiB,
then 3 GiB only after measured allocation failures. Stop other failures for
review; retain subject reduction, exact source, serial/file/core/no-swap guards
and normal defaults. Register only qualified exact-target settings, then run
the next public formal gate. This remains independent repository validation.

The metering correction is committed/integrated as GetPaidX `657d795b` and
gateway R3 is built and uploaded at
`sha256:08e6ae82dacb41bf3ed15fe752d6a470f9d426dedee9a0e3adc837f5b53b6e8e`.
Its Docker clean/pruned audits pass and dependency layers were reused.
The reviewed manifest generator now selects that source/image and expected
revision 169, retaining all controller R1 digests. It includes only the two
disabled acceptance journals for exact owned controller cleanup. The first
read-only R3 preflight reaches a host-to-Azure database-connectivity error;
no R3 mutation occurs. Retry is running in
`/tmp/getpaidx-release-r3-plan-retry-20260930.log`. Inspect its successful plan
and bind current gateway/job/cleanup fingerprints before apply.

The operator acceptance now requires successful scoped model events with
positive token counts, and its direct-program no-model assertion covers all
configured model-provider enums. Operator typecheck passes. The next acceptance
must use a fresh identity after the R3 rollout; retain the existing failure
journals and clean their exact controllers through the reviewed manifest.
The 25-target formal follow-up runs separately through
`/tmp/emdash-snake-zeros-cold-followup-20260930.py` (session 92526), recording
controls in `/tmp/emdash-snake-zeros-cold-controls-20260930.json`; log
`/tmp/emdash-snake-zeros-cold-followup-20260930.log`. No new profile bindings
have been installed until that measured group is qualified.
