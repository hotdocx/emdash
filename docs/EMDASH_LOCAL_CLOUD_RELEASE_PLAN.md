# Emdash Local And Cloud Release

Date: 2026-09-29
Status: complete feature release; independent reference CI follow-up remains open

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
| R3 | Local gateway and three controller-family builds; reviewed additive schema, pool/job mapping and healthy gateway rollout | Complete: gateway R3/revision 173; three locally built controller R1 digests deployed |
| R4 | Hosted OAuth catalog, immediate task, direct scientific program, preview, retained artifacts and export smoke; exact fixture cleanup | Complete: `execution-sep30-r6`, browser/reopen/offline replay, independently verified controller/credential cleanup |
| R5 | Integrate and push Emdash; publish a new npm version with the existing exact-artifact provenance workflow | Complete: 0.4.0, tag/source `618fdb2e`; public registry artifact verified |
| R6 | Integrate and push private Arrowgram source; dry-run then publish allowlisted OSS mirror; validate plugin packages | Complete: private `5ffaddf4`, public `990bffbf`; both CI runs pass |
| R7 | Prepare versioned portal JSON/skill ZIPs, source packages, worksheet, demo script, screenshots, checksums and release evidence | Complete: 57 files sealed, 10 included ZIPs verified, convenience ZIP in Downloads |
| R8 | Synchronize SOPs/ledgers and report published identities and remaining portal-only actions | Complete; reference CI is a separately recorded follow-up under the user's September 30 direction |

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

## Corrected rollout and complete API/reopen qualification

The R3 preflight retry passes with zero schema drift/live sessions and one
exact disabled-acceptance controller target. The guarded update reaches
healthy revision 171 on gateway
`sha256:08e6ae82dacb41bf3ed15fe752d6a470f9d426dedee9a0e3adc837f5b53b6e8e`.
All four schedules are restored, every write is confirmed, and the old R2
acceptance controller is deleted. Independent SDK checks confirm gateway/job
templates, preserved configuration/secret references, exact controller 404
and synchronized private runtime env. Receipt:
`reports/env/workspace-executions-deployed-r3-20260930.json` in GetPaidX.

Hosted `execution-sep30-r3` passes all API/program/Codex/reopen checks. A scoped
successful OPENAI/gpt-5.4 event records 10,812 prompt/29 completion tokens;
direct programs use no model provider and scheduled automation count is zero.
The new session reads the original retained result. Browser compute/reuse,
one-assumption internal construction and mathematical source editing/stale
result display pass. The operator missed the twenty-minute browser deadline
before final export/screenshots; the script safely closes/revokes/disables its
own fixture with no cleanup failures. Do not call that overall run successful.
Its partial hosted recording is labelled as such. Operator browser allowance
is now explicitly sixty minutes. Fresh `execution-sep30-r4` stops before
principal creation at a host-to-Azure connection error. The operator now uses
an explicit fifteen-second connection/pool timeout in its own process, without
changing the canonical or deployed database URL. Fresh `execution-sep30-r5`
reaches workspace start, then stops at a transient `CONTROLLER_UNAVAILABLE`
inspection response; its cleanup completes. The operator now polls only the
read-only inspection for at most three minutes after start/reopen, without
repeating workspace creation. The script typechecks, and a fresh complete
`execution-sep30-r6` run is active with the same credit bounds and stronger
token accounting. Its log is
`/tmp/getpaidx-hosted-execution-acceptance-r6-20260930.log` (session 45520).
Use `reports/env/hosted-browser-cli-r6.mjs` once its private handoff is ready.
The
attended allowance is at most six new controller starts across these attempts;
R1/R4 make no starts, R2/R5 make one each and R3 makes two. Complete captures and the
done marker before the sixty-minute deadline. The old R3
controllers remain exact cleanup targets after the active fixture finishes.

R2's captured hosted program independently replays in a network-disabled
container under Node 22.23.2: `result.json`, `retained.json`, `internal.json`
and `plot.svg` match byte for byte. The final successful run/export still needs
its own corresponding artifact evidence.

All 25 cold native-snake controls complete: 23 pass at scoped GC/2 GiB and
two exactness reviewers require the existing 3 GiB/90s profile. Only their
25 exact bindings are installed, bringing the override count to 141. The
resource ledger records every receipt. Complete tooling passes at receipt
`tooling-20260930T113011Z-7286298fad7943939798c660fbf7da1a`.
The qualification is committed/integrated/pushed as `d946d6ab`; public run
`36712188754` is active. All jobs except formal have passed at the latest observation, including
TypeScript. Preserve that run by keeping later
documentation checkpoints local until it completes. No mathematical source,
checker or default-limit change is included.

## September 30 complete hosted acceptance

`execution-sep30-r6` completes with `ok: true`, `browserCompleted: true` and
no cleanup failures. Fresh OAuth sees MCP 0.3.0, 62 tools and catalog 275/24.
Compute/reuse/internal, idempotency, stale-input rejection, cancellation,
immediate real Codex execution and project reopen all pass. Its successful
scoped OPENAI/gpt-5.4 event records 10,802 prompt/29 completion tokens, totaling
10,831; billed cents round to zero. Scheduled automation count remains zero.
The operator revokes credentials, closes its own sessions, cancels its private
fixture and disables its principal; unused non-cash credit is reclaimed.

Browser compute/reuse and one-assumption Core construction pass. Editing
mathematical input marks the retained result stale; restoring the source
restores the current-source label. Export, reload persistence and inspected
desktop/mobile layouts pass; mobile width 390 has scroll width 375. Browser
console records zero errors/warnings. The operator's 60-second export wait
expired, but the application finished the paged export and downloaded the ZIP;
this is not a failed application export. The completed 16-member ZIP has
SHA-256 `d6f0cebe82eed48bcc114213e8976f4182604f9e277f25044afa00987ebda154`.

Both this browser ZIP and the API capture independently replay in a
network-disabled 512 MiB/no-swap container using captured Node 22.23.2 from
`controller@sha256:2b3f8a45f270be63751792f67ab721d64c8f7d311fc7395c52f55de1cb2e3e13`.
All four result/retained/internal/SVG artifacts match byte for byte. Hosted
screenshots, automated browser recording, ZIP and safe receipts are copied to
Downloads `hosted-acceptance/`. The recording is labelled as scientific browser
evidence; the complete portal conversation/demo remains an operator recording.
The R4 journal confirms failure before principal creation; it has no user ID.

Final exact controller cleanup is being planned through the existing guarded
rollout helper using the same gateway/controller digests and R3/R5/R6 identity
journals. No new image build is needed. Public run `36712188754` has passed
TypeScript and every other job except the still-running formal aggregate.
Keep later documentation checkpoints local until that run completes.

## Latest public CI and cleanup follow-up

Run `36712188754` finishes with all gates passing except formal, which reaches
211 checks and fails allocation in native window-left homology (29.006s).
Two source-identical cold target controls and the whole connecting-comparison
consumer qualify two exact resource bindings, recorded in the resource ledger;
normal defaults and formal source remain unchanged. Fresh public validation
is required. The GetPaidX cleanup attempts stop before mutation at database
preflight; a bounded query succeeds in 8.792s. Its existing rollout helper now
uses 15-second operator-only connect/pool budgets while preserving exact live
URL identity checks and all runtime settings. Six focused suites/92 tests,
typecheck and source/script lint pass at checkpoint `aa15f78d`, integrated into
canonical master. A clean guarded cleanup retry is active with the same images.

## Deployment Closeout And Completion Audit

The final guarded cleanup succeeds at healthy revision 173 using the same R3
gateway/R1 controller images. All four job schedules are restored; every write
is confirmed. Independent fingerprints verify config/secret preservation and
canonical runtime env. The exact acceptance controller returns 404, retaining
its UNAVAILABLE history, provider reference and five terminal session/assignment
histories; NFS data is preserved.

The independent credential audit finds that the operator helper's OAuth cleanup
had omitted generated workspace/tool PATs. Exact disabled fixture ownership is
rechecked, then 118 PATs are revoked. The ignored helper now performs that step
and conditions its completion flag on success. Final independent verification
finds zero live sessions, active PATs, OAuth tokens/codes and positive test
allowance for every fixture; R4 has no principal. R5 retains a one-cent late
usage debit. Evidence is private GetPaidX
`reports/env/workspace-executions-final-verification-20260930.json` and
`reports/env/workspace-executions-pat-reconciliation-20260930.json`.

R1–R6 deployment/publication and hosted acceptance requirements are satisfied.
R7 files are prepared with actual hosted media and safe captured-run replay;
portal scan, conversation recording if required, review and approval/publish
are operator handoff actions. GetPaidX AGENTS/README/current operations and its
living plan now point to deployed 0.3.0/62/275/24 and revision 173.
The source-identical two-target resource correction is committed/integrated/
pushed at `72812f3e`. Public run `36720083359` passes all jobs except the
still-running formal aggregate at the latest observation. Keep this goal
active and later documentation checkpoints local until that required job
completes; do not claim a fully green repository or completed release goal yet.

## Sealed Portal Bundle

The Downloads handoff contains 56 hashed files, including ten integrity-checked
ZIPs, actual hosted desktop/mobile screenshots, automated scientific browser
recording, portable captured run and safe offline/deployment receipts. The
submission JSON matches its checked source byte for byte. Archive/path checks
and high-confidence credential scans pass; every `SHA256SUMS` entry verifies.
The convenience archive is
`/home/user1/Downloads/emdash-getpaidx-release-20260929.zip` (16,440,375 bytes),
SHA-256 `3d5a3f0d9c24c02971644f23add56d2e165609730206ed6245a41e030b6c6e3d`.
Its adjacent `.zip.sha256` verifies that archive. This version explicitly
labels the remaining public formal-CI result as pending; after that result,
refresh the evidence and reseal hashes before claiming complete qualification.

GetPaidX final documentation checkpoint `261325d2` is integrated into clean
canonical master. GetPaidX has no configured remote. The standalone portal
upload/review actions remain operator handoff. No hosted build/push/deploy,
API/browser acceptance, artifact replay or fixture cleanup is still running.
The only active automated release requirement is public formal CI
`36720083359`; follow its terminal outcome, preserve source pins and record
any additional measured correction rather than suppressing a failed check.

## Persistent Tracker Handoff

At the final September 30 status inspection, `get_goal` reports `blocked`
(despite the earlier deployment/connectivity/cleanup conditions now being
resolved). The available goal tools cannot set status back to active; resumption
is controlled by the user/system. Work under the user's Continue instruction
has completed deployment, acceptance, cleanup and the sealed handoff. The
remaining public formal gate continues independently in GitHub Actions.
Do not mark the objective complete before its terminal result, and do not
repeat the already-finished hosted acceptance or deployment on resume.

## Latest Formal Failure And Bounded Follow-up

Public run `36720083359` finishes with every job passing except formal. The
left-window correction passes in that run; it then reaches 215 checks and
fails allocation at `emdash3_2_one_cat_native_window_snake_right_kernel_quotients.lp`
(exit 134, 28.213s). Four current default-profile descendants are selected:
right kernel quotients, right kernel pair, right kernels and its reviewer.
Serial source-identical no-object controls are running through the standard
guard, with default 2 GiB/90s then scoped GC and measured 3 GiB if needed.
The driver stops any unexpected failure for review. No new profile binding or
formal source change is installed before qualification.

Background driver `/tmp/emdash-window-right-cold-followup-20260930.py`, log
`/tmp/emdash-window-right-cold-followup-20260930.log`, results
`/tmp/emdash-window-right-cold-controls-20260930.json`, tool session 41019.
After controls finish, check the real cold right-homology consumer at its
existing explicit 3 GiB/90s profile, synchronize exact bindings/resource
ledger, run owning docs/tooling checks, checkpoint/integrate/push, and require
another complete public validation. Deployment and fixture cleanup remain
finished; do not rerun them. Keep the portal bundle's CI evidence and hashes
synchronized with this new failure/pending qualification.

After updating the CI evidence, the re-sealed convenience ZIP has SHA-256
`667fac4378abc8368a3d6f030a896cf96fcb003ae5036d9d319f6ae9b219952d` (16,440,458 bytes); the earlier bundle hash is superseded.

The first right-window target reproduces allocation failure at default 2 GiB
(24.720s), scoped GC/2 GiB (38.023s) and GC/3 GiB (61.354s). The driver stops
for review, as required. Under the existing standing resource authorization,
only this owner is now replaying at the existing explicit 4 GiB/90s GC profile;
defaults, formal source, subject reduction and no-swap/serial/file guards are
unchanged. Receipt JSON will be
`/tmp/emdash-window-right-owner-4g-20260930.json`. The remaining three targets
and real consumer still need their own measured qualification before bindings
or another public run. The four-target driver is stopped, not still running.

## Current Background Handoff

The reviewed owner passes cold at 4 GiB/90s with scoped GC in 72.376s,
maximum child RSS 3,540,324 KiB, receipt
`20260930T141608Z-18a17d6272da41a785c619c87df90f0b`. Its source pin matches
the prior failed controls. Default/GC 2 GiB and GC 3 GiB failures remain
recorded; no new formal binding is installed yet.

The import inventory identifies eleven exact targets: four current defaults
and seven existing 3 GiB/90s targets. A new serial background driver reuses
only the pinned successful owner receipt, then checks the remaining defaults
at scoped GC/2 GiB → 3 GiB → 4 GiB as required, and current 3 GiB targets at
3 GiB → 4 GiB as required. Every child retains 90 seconds, subject reduction,
the normal guard, file/serial/no-swap restrictions and source-identical cold
inputs. Any allocation failure at 4 GiB or non-allocation failure stops for
review; standing authorization permits a separately measured extension if
needed. The actual right-homology/connecting consumers are included in this
inventory. Do not select metadata until the relevant whole group is qualified.

Driver `/tmp/emdash-window-right-import-controls-20260930.py`; log
`/tmp/emdash-window-right-import-controls-20260930.log`; results
`/tmp/emdash-window-right-import-controls-20260930.json`; session 31005.
Expected terminal line: `Completed all 11 cold import targets.` Review the
receipts rather than treating the last log line alone as qualification.
On interruption, restart this source-pinned driver only after confirming the
old process ended; it replays the controlled sequence and checks each receipt.
Do not restart the superseded four-target driver, whose 3 GiB ceiling has
already been rejected. After a qualified group, synchronize exact overrides,
resource ledger and current CI evidence; run owning tooling/docs gates,
checkpoint/integrate/push and verify fresh public formal CI. Deployment,
fixture cleanup and portal artifact preparation need no repetition.

Current sealed handoff hash after that evidence update: `4e6239deed92245e357c4b7c73d24c9369cd2dd20037f1513b5957bf123dd4a0`
(16,440,525 bytes). Earlier convenience ZIP hashes are historical.

## Qualified Right-Window Metadata And Resumed Goal

The goal is explicitly resumed and `get_goal` reports active. The previous
turn completed hosted closeout and produced new allocation evidence; this
continuation verifies the live driver, not a stale process marker. The user's
latest instruction also reaffirms committing progress and fast-forwarding
canonical main. Main is already fast-forwarded through `b22bfb31` while the
relevant metadata is qualified.

All eleven cold import controls complete. Source pins match the current
checkout; three owners plus the right-kernel reviewer require 4 GiB, while
seven existing 3 GiB/90s consumers remain unchanged. Pair/reviewer deadline
replays at 4 GiB/180s pass in 91.939/94.318s, exceeding their earlier strict
90s-run durations and justifying deadline headroom. Four exact bindings are
installed (147 total), with full measurements in the resource ledger.
No formal source/default-limit change is made. Run owning tooling/docs gates,
checkpoint, fast-forward main and push, then verify the fresh public CI result.

Current-state audit also confirms npm 0.4.0 registry integrity/provenance and
exact bundled tarball SHA-256, peeled tag source `618fdb2e`, successful publish
workflow, private/public Arrowgram heads `5ffaddf4`/`990bffbf`, and healthy
gateway 173 with unchanged R3 image. Hosted acceptance/replay/fixture cleanup
receipts remain valid for that unchanged artifact; they are not repeated.

## Current Public Validation

The qualified metadata is committed as `86ae3a78`, fast-forwarded into clean
canonical main and pushed. Docs and complete owning tooling gates pass at
receipts `docs-20260930T144643Z-1ae73e9694f440dfb70192cd8a4f511b` and
`tooling-20260930T144642Z-38df7973a1024beb98754e3ae5602738`.
Fresh public run `36731930747` is verified in progress at exact source
`86ae3a78b9474e95ab61b1d33bcad041147adbbb`. All local cold/deadline controls
are now terminal and green; no local checker is still running.
Keep this goal active and inspect that run's terminal outcome. Preserve its
execution by keeping later documentation checkpoints local while it runs.
A verified wait on that live job is progress toward its required outcome,
not a reason to mark the goal blocked. Any next failure needs its own evidence;
any complete result needs the final requirement-by-requirement release audit,
updated bundle evidence/checksums and final doc integration/publication.

## September 30 Boundary Allocation Follow-up

Public formal job `109943660587` completes unsuccessfully after 246 checks:
`emdash3_2_one_cat_boundary_representatives.lp` allocation failure (exit 134,
30.559s). The prior right-window fixes pass in that run. Every completed
non-formal job passes; scale-conformance job `109943660534` remains live in
system dependency setup, with its pinned OCaml step completed at 14:50:18Z.
The log API returns 404 while that job is live; this observation failure is
not terminal and does not authorize an observation-only restart.

The default-profile import inventory contains six exact targets: boundary
representatives, middle homology representatives, cycles, exactness and the
homology-representative/middle-cycle reviewers. Standard serial source-identical
cold controls are running at 2 GiB/90s default GC, then scoped GC at 2 GiB and
measured 3 GiB if needed. Stop unexpected outcomes for review; standing resource
authorization remains in force. Defaults, source, checker, subject reduction,
serial/file/no-swap guards are unchanged. No new binding is installed yet.

Driver `/tmp/emdash-boundary-cold-followup-20260930.py`, log
`/tmp/emdash-boundary-cold-followup-20260930.log`, results
`/tmp/emdash-boundary-cold-controls-20260930.json`, tool session 99352 at launch. After the
measured group qualifies, verify the real consumer and source hashes, select
only measured exact bindings, run owning checks, checkpoint/fast-forward main,
and push a fresh validation at an attended boundary. Keep current live-job
state distinct from the terminal formal failure. Hosted release/cleanup and
portal artifacts need no repetition.

## Qualified Boundary Metadata And Bounded CI Setup

All six controls and both real consumers pass with current source pins.
Five exact targets select GC-only 2 GiB/90s and one selects 3 GiB/90s,
bringing the override count to 153. The resource ledger records measurements
and both consumer receipts. No mathematical source or normal default is changed.

The live scale-conformance job has not completed system-dependency setup after
more than 90 minutes. The workflow's existing APT step had no step deadline or
explicit finite transport retry/timeouts. Bound only that step to ten minutes,
three retries and 30-second HTTP/HTTPS connect/data timeouts, using noninteractive
installation. Installed packages and verification pins are unchanged; the local
APT primary manuals confirm those options. This produces a visible terminal
setup failure rather than consuming the entire gate window. It is CI setup
reliability work, not a cloud runtime/opam version migration.

After owning checks and a clean checkpoint, fast-forward/push main. The new
source validation intentionally supersedes the run whose formal job is already
terminal/failed; it also replaces that run's still-live dependency-setup job.
This is validation of new qualified source, not a restart based solely on an
observation timeout. Preserve the old run/error evidence. Complete public
validation and the final release audit still remain required.

## Current Qualified Boundary Source

The new qualification/setup change is committed as `5a9c4f61`, fast-forwarded
into clean main and pushed. Complete owning tooling passes at
`tooling-20260930T162817Z-54807154643245ef8469a5485eebf800`; docs passes at
`docs-20260930T162816Z-d8a38a9c0c534370b7d19f4ab489be0d`. Changed shell syntax
and APT option parsing also pass. Fresh run `36744636789` is verified live at
exact source `5a9c4f610cdbdb375dcc5f412b5c0ef02d06fd3a`. The old run is now
terminal/cancelled due to this intentional new-source supersession; retain its
formal failure as evidence. No local checker is still running. Preserve the
new run and keep later documentation checkpoints local until its result.
The bundle now describes this source and pending run accurately.

Current convenience ZIP: 16,440,578 bytes, SHA-256 `665bc4a133c966567e10a8169186aede121a987724fd128d1621a2524c130a5e`.

## User-Directed Scoped Closeout

On September 30 the user explicitly requests completing the remainder of this
goal now and allowing existing remote CI to finish for later follow-up. This
restores the accepted feature boundary: LC-1–LC-4 qualifies the supported
polynomial/relation consumer, not a broad formal-profile transfer. The accepted
implementation plan and root proportional SOP already make that distinction.
Repeated full reference sweeps became an unnecessarily broad release blocker;
this closeout does not pretend that the pending reference result is green.
[Reference CI follow-up](EMDASH_REFERENCE_CI_FOLLOWUP_2026-09-30.md) preserves the
live run, findings, operational changes and later review procedure. The existing
run is left intact. No new aggregate is needed for this documentation tranche.

### Requirement-by-requirement closeout audit

| Requirement | Inspected authoritative evidence and result |
| --- | --- |
| Settled architecture and foundational strategy | Strategy, README and completed LC-1–LC-4 plan describe TypeScript library APIs, generic execution, distinct program/Codex adapters, durable projects, mini-app views and explicit proof/assumption boundaries. Broader science and standalone metatheory remain a roadmap. |
| Generic immediate tasks and program lifecycle | GetPaidX implementation/qualification ledger and complete isolated regression at gateway source `657d795b` cover authorization, idempotency, cancel/process-tree handling, stale source, disconnect/restart outcomes and retained results. Hosted R6 independently executes a real immediate Codex task with 10,831 scoped model tokens and zero scheduled automation runs; direct programs create no model events. |
| Local/cloud Emdash and installed packages | Full 481-suite/2,971-test TypeScript boundary, packed ESM/CJS/declaration/browser consumers, copied local CLI/SDK/plugin checks and installed-cache parity qualify unchanged local/math code. Hosted compute/reuse/internal use the same portable program/data format; the optional internal route retains one explicit computed-equation assumption. |
| Hosted scientific browser and persistence | Actual R6 browser receipt/inspected desktop/mobile media cover compute, reuse, source editing/stale label/restoration, export, reload and no overflow. Actual reopened session reads the original retained result. CLI/SDK and scientific browser evidence are labelled accurately; a full portal conversation recording, if requested, remains operator work. |
| Local builds, schema and deployment | Additive schema review/application; locally built/pushed gateway R3 and three controller R1 immutable digests; independent SDK/config/job/schedule/secret-reference verification and healthy current revision 173. No ACR build or data-loss override was used. |
| Operational fixture cleanup | Private independent verification confirms exact acceptance-app 404, retained histories/NFS, disabled principals, no live sessions, unrevoked PATs, OAuth tokens/codes or positive allowance. 118 generated fixture PATs are revoked; the one-cent late debit is retained. |
| Emdash publication | Exact tag source `618fdb2e`, successful npm workflow `36521885693`, public 0.4.0 provenance and registry/bundle integrity; tarball SHA-256 `999649a3f0869e8322e4a99adfd7da7d3473cbcfdcc826805b4e13e8ca4b9f58`. Published package checks are its owning gates, independent of the later full reference sweep. |
| Plugin source publication | Current private/public Arrowgram heads `5ffaddf4`/`990bffbf` and their passing CI; allowlisted exports preserve private SaaS material. Local/cloud plugin manifests and bundled source/skill archives are inspected. |
| Portal handoff | Downloads JSON equals checked source byte for byte; 62 descriptors/annotations, five positive and three negative cases, both skill ZIPs, local plugin/source/template/npm archives, worksheets/demo script, hosted media/export and safe receipts. Ten included ZIPs pass integrity/path checks; replayed four-file artifacts match twice; checksums and credential scan pass. Portal scan/review/approval/publish remain the explicit operator handoff. |
| Checkpoints, main and unrelated work | Qualified tranches are committed and main fast-forwarded/pushed. GetPaidX canonical master is integrated at `261325d2` with no configured remote. Unrelated native-nerves and Arrowgram consulting work is preserved. Final changes are documentation only and receive owning doc checks. |

All feature-release requirements R1–R8 are satisfied. Final documentation and
bundle evidence explicitly preserve the pending reference CI as an independent
follow-up. This completion is not a claim of whole-repository green CI or a
consistency certificate. A documentation-only final commit uses the supported
skip marker after local doc qualification to avoid starting another aggregate
or superseding the existing run; it changes no executable/validation policy.

Final scoped handoff: 57 hashed files, ten verified included ZIPs, zero
credential findings. Convenience archive 16,442,739 bytes,
SHA-256 `611cb4acce27be1307c802e85a4f6c2c7ae9df4b4f776fc80c076e4677369fdf`. Adjacent checksum and all SHA256SUMS entries verify.
GetPaidX closeout documentation is committed/integrated at `7da6b3c7`.
