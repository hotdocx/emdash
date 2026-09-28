# Algebra Goal Assistant: Local Main Integration

Date: 2026-09-28 UTC

Status: complete; locally integrated into main at merge checkpoint `5da39dcf`

Main baseline: `1b9cb02ac161458319d91fc6c53606ebd744c84d`.
Donor: `50ccee2f8d15e6a62f5db8748805e03ec485581f` on
`goal/algebra-goal-assistant-plugin-v3.2`.
Shared ancestor: `37ce19d5c727f8d1c5579445981a8f4f6d3f32d4`.
Integration branch: `integration/algebra-goal-assistant-plugin-v3.2`.
Worktree: `/home/user1/emdash1-goal-assistant-plugin-integration-v1`.

## Objective And Authority

The user accepted review and local integration of the completed plugin branch
into main with appropriate combined validation, explicitly without pushing.
Preserve both branches' history, the qualified action-profile implementation
and book, and the plugin's existing mathematical and operational boundaries.
Use local checkpoint/merge commits in this dedicated worktree, then
fast-forward main only after qualification and clean-state verification.

The [plugin plan](EMDASH_ALGEBRA_GOAL_ASSISTANT_PLUGIN_PLAN.md) and
[product orientation](EMDASH_ALGEBRA_GOAL_ASSISTANT_ORIENTATION.md) own the
donor scope. The [handoff](TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md), root
`AGENTS.md`, [formal SOP](../emdash2/AGENTS.md),
[DevOps guide](DEVOPS.md) and [Git workflow](PERSISTENT_GOAL_GIT_EXPERIMENTATION.md)
govern this integration. The donor's earlier aggregate waiver records its
historical qualification. This integration completed one full TypeScript run;
after its two article-pin failures were repaired, the user explicitly directed
that no further full aggregate be run. Final qualification combines that
recorded run with the focused repair checks below; it does not relabel the
failed aggregate as a passing run.

No mathematical owner, transferred semantic profile or runtime/proof rule is
changed. The inherited article-provenance pins receive the exact-content
review recorded below. Native exact computation stays distinct
from approximate views and the explicit computed-equation assumption used by
internal construction. No cloud transport, public release, plugin-cache
reinstallation, history rewrite or worktree cleanup is selected.

## Review And Validation Plan

| Slice | Required result | State |
| --- | --- | --- |
| Git and dependency review | Preserve both ancestries; inspect all 34 donor paths and the two auto-merged documents; frozen pnpm bootstrap | Clean merge prepared; bootstrap and workspace check passed |
| Mathematical reuse | Preserve actual retained coefficients, independent relation checking, integer interpretation and explicit assumption status; fresh Singular/Lambdapi consumer | All six external-module tests pass, including real Singular and guarded LP positive/negative controls |
| Goal service | Workspace source/revision controls, native/internal construction, worker cancellation/limits and CLI/MCP catalog agreement | All 22 donor tests pass; additional contributor-CLI regression fails before the correction and passes after it |
| Portable delivery | Build current bundle; copied runtime and copied plugin execute outside checkout; plugin/skill schemas validate | Build, validators, copied CLI and real SDK STDIO acceptance pass; 83 source inputs and both bundles rehashed |
| Combined TypeScript | Complete `check:ts`, with any failures diagnosed and repaired under the user's validation direction | Completed: 2,881 pass, two inherited article-pin failures, 88 skips; 15 owning tests pass after repair; user forbids another aggregate |
| Package/tooling/print | Packed package checks, script/registry tooling and affected renderer checks; preserve existing dependency versions | Tooling and package gates pass; final package replay after CLI repair passes; both article/book renderers pass |
| Documents and handoff | Update this ledger and current handoff, inspect exact staged diff and artifact/source identities | Qualification, failure/fix scope and aggregate waiver recorded; document checks and identity audit pass |
| Local main integration | Validated merge checkpoint, clean main ancestry check, fast-forward and final clean verification | Merge `5da39dcf` retains both parents; local main fast-forward, frozen bootstrap and runtime startup verified |

Logs live in `emdash2/logs/plugin-integration/`; generated runtime lives in
ignored `plugins/emdash/dist/`. Current-source input hashes and test results
will be retained with the final checkpoint evidence.

The conservative gate selector currently treats the new plugin/marketplace
paths as unclassified and selects all gates. This integration uses the
repository's proportional-validation policy and explicitly runs the affected
gates plus the delivery checks above. It does not change gate-selection policy.
Recent complete formal qualification is carried forward only after verifying
that the entire Lambdapi source, checker, runner and resource-profile inputs
are unchanged. The focused live external-module consumer is checked afresh
against that action-profile baseline. Unchanged book/PDF sources and qualified
artifacts retain their existing evidence; the dependency install receives
fresh renderer checks rather than an unnecessary PDF export.

The complete TypeScript run uses the previously qualified 4 GiB V8 heap
setting through `NODE_OPTIONS`, with the gate's existing one-hour deadline.
Each live Lambdapi probe retains its normal serial, memory and deadline guards.
Failures remain evidence and are diagnosed at the smallest affected boundary.

## Initial Review

The five donor commits add six workspace tools, the corresponding CLI,
ordinary inert JSON source/artifacts, and portable TypeScript authoring.
`algebra_relation_module_reuse.ts` extracts the existing external-module
construction path; its external adapter retains its source, witness, names,
decision and freshness contract. Native workspace reuse checks retained
coefficients instead of rerunning membership. Internal reuse adds one
recorded computed equation and constructs a typed whole complex and action;
it does not add a Core projection reduction or claim exactness/homology.

The only tracked dependency addition is pinned MCP SDK `1.30.0` and its
lockfile closure. Main's already integrated source-alignment metadata is
retained. `README.md` and the TypeScript handoff merge without conflicts and
keep both the action-profile qualification and plugin product orientation.
The source plugin and skill validators pass without manifest edits.

## Contributor CLI Correction

An additional smoke test from `/tmp` found that the new `scripts/emdash goal`
route resolved `ts-node/register` from the caller's directory and failed before
executing a command. This did not affect the standalone copied runtime. The
new regression runs the real contributor launcher from an unrelated temporary
directory and initializes a relative `mathematics` root there. It reproduces
the missing-module failure, then passes after the goal route selects its
checkout's loader and `tsconfig.json` explicitly. The caller's working
directory is preserved. Other existing launcher routes are unchanged.

The first aggregate was deliberately cancelled through its owning DevOps
runner before changing source: receipt
`typescript-20260928T031929Z-e8054ccaaf064836a9e5b37403d9ef4d` records `cancelled`,
exit 130. Its terminated child output is not an independent test failure.
The corrected aggregate is
`typescript-20260928T032620Z-48fb5ab814284ca18f4ad9df4d9b47ed`.
Focused evidence is `cli-cwd-before.log` and `cli-cwd-after.log` under the
integration log directory; the latter passes its one selected test in 4.708s.
Shell syntax also passes. The earlier tooling gate's script-input snapshot
precedes this localized correction; its focused shell/behavior follow-up and
the corrected full TypeScript gate cover the changed route.

## Qualified Evidence So Far

- Frozen bootstrap passes using Node 24.11.1 and pnpm 11.16.0; all 455 packages
  are reused from the shared store, with an independent link graph.
- Goal workspace/MCP/construction: 22 tests, zero failures/skips, 17.367s.
- External-module reuse: six tests, zero failures/skips, 23.312s. Live positive
  construction/projection/action and different-coefficient rejection run
  against the current action-profile source under the existing 60s probe bound.
- Copied runtime and copied plugin checks pass fresh; both use ordinary
  temporary mathematical workspaces and preserve source/result identities.
- Tooling: `tooling-20260928T032104Z-81ca9abec6184edcafa378de07e8534a`,
  `passed-fresh`, 69.712s, before the launcher-only correction.
- The initial package gate passes in 31.393s; the final post-correction package
  gate `package-20260928T032622Z-889edac940914b2f8fb86ddaeb07b572` passes in
  9.101s. It covers packed ESM/CJS/browser/algebra consumers and
  release-preflight tests without any publication.
- `print:check` passes both registered documents: 19-page article and
  416-page book, with no console/page/request/render errors. No book or PDF
  content is changed by this integration.
- The standalone browser reviewer gate
  `reviewer-20260928T032943Z-f20edd6c6159423cbd9c03e7e82f6b8d` passes fresh in
  9.871s after its fixture-owned npm install. This does not create a contributor
  npm lock or change the shared pnpm workspace.
- Exact comparison covers 1,533 formal source/runner/profile/toolchain files
  against current main, with zero differences. No LP source is edited.

Current portable command SHA-256:
`2d6eb3795c6758af46e2e6d0bd4f9f7c02965aca27d9dd1ca7b47af41ba9c8d3`.
Authoring bundle SHA-256:
`d86c123ad02213dcbdd7ef555f31687c3d944aa33efb6cb727d7beabcc7c1caa`.
Both match the recorded existing installed plugin cache byte for byte; no
cachebuster or reinstallation is needed for this launcher-only correction.

## Article Binding Failure And Reviewed Repair

The complete combined run finished all 2,971 tests in 481 suites in
1,827.415s: 2,881 passed, two failed, 88 opt-in tests skipped, none cancelled.
Its receipt remains failed. Both failures were in `AI-PAPER-1B1` research-file
materialization: `ai_research_overview.ts` still pinned the earlier article
bytes after action-profile commit `8ea6c86b` updated two exposition passages.
A focused control on untouched main `1b9cb02a` reproduces the same failure.
The plugin's tests and the contributor CLI correction passed in the aggregate.

Review compared the exact formerly pinned article from `37ce19d5` with current
main. Only the Gray classifier/arrow description and higher-category open
boundaries changed. Both Arrowgram bodies are byte-identical. The proof-demo
source, proof profile, declaration bindings and complete/open proof artifact
hashes remain unchanged. The Node materializer and browser recheck freshly
agree on the same four blocks and proof statuses after the repair.

The document binding advances to v5, with document revision
`2026-09-27-action-profile-draft` and current article digest
`sha256:c9b44fda0e2d8083d39e2926896ee45ecd54a2beaf26c7014acedeb4e38d5059`.
Its management-source digest becomes
`sha256:783c792754b7a08d31ae40964be6d0cbedcbc856d616f365ee1ad541406839e8`.
No diagram/proof pin, proof term, article byte, mathematical source or
fail-closed guard changes. The complete owning CLI/research-file suite passes
15 tests without skips in 5.243s, including arbitrary prose/diagram/proof drift
rejection. `article-pin-review.json`, `article-binding-reviewed.json`,
`article-pin-main-control.log` and `article-binding-focused.log` retain the
comparison and actual results under the integration log directory.

User direction after this repair: **do not run another full aggregate**.
Finish with typecheck, changed-file lint, document checks and exact Git/input
verification. Earlier package, portable-runtime, formal and print results keep
their original snapshots; unaffected implementation/artifact identity is
verified rather than asserting a later full run occurred.

## Final Qualification And Checkpoint

After the pin repair, root typecheck and changed-file ESLint pass. Document
hygiene passes with 151 resolved local links. Comparing the aggregate receipt's
actual input map with the current tree identifies exactly the two reviewed
research-binding files; no other input drift is present. The earlier tooling
receipt differs only at the separately tested contributor launcher.

All 24 implementation inputs checked in the completed aggregate retain their
recorded bytes. The portable build still verifies all 83 source inputs and
both bundle hashes. All 80 unique application sources embedded in the packed
package's source maps match current files. The book/article PDF bytes remain
identical to main's qualified artifacts. The browser materializer parity test
qualifies the metadata follow-up; the earlier browser gate is not relabeled
as a fresh run after that edit.

The user explicitly permits the fixes and directs: “ensure you don't redo
another full aggregate checks”. Accordingly, the acceptance evidence is the
completed 2,971-test run plus the focused repair checks, with its two original
failures preserved. No second full aggregate follows the article-pin repair.
All scoped functionality is qualified under that explicit validation boundary.

## Local Integration Receipt

Merge checkpoint `5da39dcf56f899c5238f561ba459698725e26609` retains main
`1b9cb02ac161458319d91fc6c53606ebd744c84d` and donor
`50ccee2f8d15e6a62f5db8748805e03ec485581f` as its two parents. All 39 committed
paths match the reviewed staging manifest
`emdash2/logs/plugin-integration/checkpoint-manifest.json`; no unrelated or
unstaged files were included. No Lambdapi/book source or PDF changed.

After verifying clean main at the pinned baseline and its ancestry, local
main was advanced with:

```bash
git merge --ff-only --no-stat integration/algebra-goal-assistant-plugin-v3.2
```

Main's frozen bootstrap and workspace contract pass with its own dependency
links. A fresh portable-runtime build on main matches all 83 qualified source
inputs and both bundle hashes above. The actual main `scripts/emdash goal
capabilities` launcher works from `/tmp` and reports all six commands.
These are setup/build/startup operations, not a repeated aggregate. Main and
the integration worktree are clean at the merge checkpoint.

This final receipt is a documentation-only successor checkpoint. The donor
branch remains unchanged, and all worktrees remain available. No push,
publication, cloud action, installed-plugin update or cleanup was performed.
