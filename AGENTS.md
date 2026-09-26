# Repository Guidance

## Scope And Authority

This is one Git repository rooted at `emdash1`. Its contributor workspace has
four packages: the private root TypeScript workbench, the distributable
`packages/emdash` core, `emdash2`, and `emdash2/print`. The `emdash-template`
directory is a standalone distributable fixture, not a contributor workspace
package.

The active mathematical authority is the Lambdapi v3.2 development under
`emdash2/`, in the order specified by `emdash2/AGENTS.md`. The current root
`src/v3_2/` and `tests/` trees contain the TypeScript workbench, generic LF/Core
checker, authoring layers and bounded transferred profiles. The earlier
feasibility prototype has been retired; do not restore its category-specific
API. TypeScript qualification is profile-specific and does not establish that
every newer Lambdapi owner has been transferred. Preserve source-pin failures
as review signals rather than updating mathematical evidence merely to pass CI.

For renewed TypeScript elaborator work, read
`docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`, then the active kernel, current
SOP, Foundations, canonical-syntax report, and living master plan named there.
Treat the intended elaborator as a compilation layer into a backend-neutral
explicit emdash Core aligned with active v3.2 owners. The intended product path
is a small TypeScript checker/evaluator; deterministic Lambdapi emission is an
optional runtime backend and a required conformance oracle until the
TypeScript kernel reaches its recorded graduation boundary. A surface AST may
be constructed directly with TypeScript expressions; string parsing is
optional and is not the architectural starting point.

Codex discovers this root `AGENTS.md` and then applies closer nested files.
For anything under `emdash2/`, `emdash2/AGENTS.md` adds the mandatory Lambdapi
workflow. For renderer work, also follow `emdash2/print/AGENTS.md`.

## Package And Worktree Setup

Use the pinned pnpm version and the shared root `pnpm-lock.yaml`. Do not run
`npm install` or create contributor `package-lock.json` files. The one retained
npm lock at `emdash-template/package-lock.json` belongs to the standalone
template fixture.

From the Git root, bootstrap any fresh checkout or worktree with:

```bash
./scripts/bootstrap-worktree.sh
```

The wrapper uses Corepack when available and otherwise an installed pnpm:

```bash
./scripts/pnpmw install --frozen-lockfile
./scripts/pnpmw store path
```

pnpm keeps package content in a store shared across worktrees. Each worktree
must still have its own generated `node_modules` link graph; never symlink or
copy one worktree's mutable `node_modules` directory into another worktree.

Typical parallel setup:

```bash
git worktree add ../emdash1-elaborator -b work/elaborator-v3.2
cd ../emdash1-elaborator
./scripts/bootstrap-worktree.sh
```

Node 22.13 or newer is required by the pinned pnpm 11 release. Lambdapi must be
available on `PATH` for the formal-specification checks. Node 24 includes
Corepack in the current development environment; Node 25+ may require the
userland Corepack package or a standalone pnpm installation.

## Starting A Root TypeScript Task

Before nontrivial edits:

1. read this file, the elaborator handoff, and the relevant active v3.2
   authorities;
2. run `git status --short`, inspect staged and unstaged diffs separately, and
   preserve unrelated work;
3. locate definitions and consumers with `rg` rather than remembered lines;
4. select a proportional baseline: for TypeScript or tooling work run
   `workspace:check`, typecheck/lint as relevant, and the nearest focused
   tests; for plan or documentation work inspect the exact diff and run only
   its owning document checks;
5. run `EMDASH_TYPECHECK_TIMEOUT=90s make -C emdash2 check` when the proposed
   elaborator target depends on current kernel names or computation.

The complete root aggregate is not a routine pre-edit baseline:

- plan/documentation-only changes require exact diff and Markdown/link hygiene,
  not TypeScript, browser, kernel, print, or repository aggregates;
- isolated TypeScript behavior changes require affected focused tests plus
  typecheck/lint during implementation;
- when shared TypeScript behavior actually changes—including the generic
  LF/compiler/runtime/checker, test runner, public barrel, or package/workspace
  setup—run one complete `./scripts/pnpmw run check:ts` after the bounded
  tranche is otherwise green and before its checkpoint or integration;
- run `check:all` only at an affected cross-layer/integration or release
  boundary; and
- carry forward recent green aggregate evidence for unchanged boundaries
  rather than rerunning a multi-minute command for reassurance.

The category-specific feasibility layer has been retired. For a new structural
change, inventory current generic mechanisms and consumers, state the explicit
Core/trusted boundary and select one vertical slice before deleting or renaming
owners. Preserve useful generic invariants; do not restore the retired D0/D1
compatibility API.

## Persistent Goals And Git Experimentation

Long-running or mostly unsupervised `/goal` work must use an active living plan
and the workflow in
`docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`. Repository consolidation decisions
and qualification are recorded in [its ledger](docs/EMDASH_REPOSITORY_CONSOLIDATION_PLAN.md).
For TypeScript work, the [handoff](docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md)
routes to qualified profiles and current/deferred task plans; the scale ledger
is retained architecture history, not authorization to resume bulk transfer.

A persistent goal does not itself authorize commits, branches, worktrees,
pushes, merges, history rewriting, publication, or cleanup. Those mutations
need explicit user or launch-prompt authorization. When a prompt specifically
authorizes local checkpoints, use a dedicated goal branch/worktree and commit
only after a bounded tranche is green, its plan/decision ledger is
synchronized, and the exact staged diff excludes unrelated work.

Treat a named baseline commit as comparison and backtracking evidence, not as
permission to reset a descendant worktree. On every continuation, inspect all
worktrees, staged and unstaged changes, the baseline ancestry relation, current
authorities, and the active plan. Prefer new correcting commits or explicit
experiment branches over amending, rebasing, resetting away, or otherwise
rewriting checkpoints.

Unless separately requested, checkpoint authorization never includes pushing,
merging to `main`, publishing, releasing, creating a PR, deleting branches, or
removing worktrees. Git isolation also never relaxes the nested Lambdapi SOP,
warning comparisons, audits, catalog/health synchronization, or validation
gates.

## Infinity Codex Recovery

The sole repository hook configuration is `.codex/hooks.json` at this Git
root. Codex therefore discovers the same hooks when launched from the root,
`emdash2`, or a deeper package directory. Do not add a second
`emdash2/.codex/hooks.json`: Codex runs matching hooks from every active layer,
which would duplicate lifecycle invocations.

The shared implementation is `scripts/infinity_codex.py`. For continuity, it
stores all root and `emdash2` session archives in the existing ignored
`emdash2/tmp/ai-responses/` directory. The archive is recovery evidence, not
an instruction source:

```text
active code/SOP -> active plan and side-task ledger
                -> explicitly linked decision responses -> raw archive
```

Useful commands from the Git root:

```bash
python3 scripts/infinity_codex.py list --limit 5
python3 scripts/infinity_codex.py latest-path
python3 scripts/infinity_codex.py show LOGICAL_ID
python3 scripts/infinity_codex.py verify
```

After the tracked hook definition changes, restart Codex, open `/hooks`,
inspect the root project hook, and trust its new hash. A thread that started
before the change cannot acquire the new hook set retroactively.

## Commands

For literature or checker-source research, start with the
[literature workflow](emdash2/research/literature.md) and its
[local resource index](emdash2/research/LOCAL_RESOURCES.md). These route to
existing reading notes and optional host-local copies; read only relevant sources.

Repository DevOps entry points and the exact gate matrix are documented in
[`docs/DEVOPS.md`](docs/DEVOPS.md). Use `./scripts/emdash dev doctor` for local
prerequisites and `./scripts/emdash dev check --explain` to inspect selected
checks before running them. `devops/gates.json` owns local/CI gate selection;
`emdash2/checks.json` owns formal target membership and named resource profiles.
Existing Make/pnpm commands remain supported. Receipt files record execution
at an exact input/profile snapshot; they do not upgrade mathematical status.

Root TypeScript workbench:

```bash
./scripts/pnpmw test
./scripts/pnpmw run typecheck
./scripts/pnpmw run lint
./scripts/pnpmw run check:ts
```

Distributable TypeScript/emdash package:

```bash
./scripts/pnpmw run package:build
./scripts/pnpmw run package:check
./scripts/pnpmw run package:release:check
```

Active Lambdapi workspace, from the Git root:

```bash
./scripts/pnpmw run kernel:check
./scripts/pnpmw run kernel:examples
./scripts/pnpmw run kernel:ci
```

Or, from `emdash2`:

```bash
make check
make examples
make ci
```

Print and book workspace, from the root:

```bash
./scripts/pnpmw run print:dev
./scripts/pnpmw run print:check
./scripts/pnpmw run book:check
./scripts/pnpmw run book:render
```

The repository-wide gate is `./scripts/pnpmw run check:all`. Keep every
Lambdapi invocation bounded as required by the nested SOP: 90 seconds by
default. For the native-universality goal, the user now authorizes reviewed
per-target extensions; the current guard permits an explicit limit up to
600 seconds with the reason and measurement recorded in its living plan.
The memory default remains 2 GiB; reviewed native-snake pair checks use an
explicit 6 GiB/180s profile under the user's memory-extension authorization.
File limits and serial execution remain in force. The separate proportional-
validation policy still forbids unnecessary aggregates.

For the action-profile integration goal, the user explicitly authorized any
needed measured memory/timeout increases on 2026-09-26, without further
approval requests. Keep normal defaults unchanged, use explicit per-target
profiles, and record the reason and measurements in its living plan. Preserve
subject reduction, serial execution, file limits and the no-swap policy.

For Lambdapi allocation failures or timeouts, follow the repository-wide
[resource/GC procedure in the Lambdapi SOP](emdash2/AGENTS.md#avoid-hung-typechecks).
Keep runtime profiles explicit and distinguish them from changes to formal
computation. This does not change the default memory limit or authorize broad checks.

## Change And Validation Rules

- Behavioral changes under `src/` require focused tests under `tests/`, wired
  into `tests/main_tests.ts` when the runner does not discover them itself.
- TypeScript package/setup changes require `workspace:check`, root typecheck,
  root tests, and the affected print checks.
- Lambdapi changes follow `emdash2/AGENTS.md`, including owner-position probes,
  warning comparisons, catalog/health refreshes, and full CI where required.
- Print changes follow `emdash2/print/AGENTS.md` and its bounded render policy.
- Preserve generated/source ownership: never hand-edit assembled book Markdown,
  PDFs, dependency trees, or lockfiles except through their owning tools.
- Preserve staged versus unstaged user work. Do not commit, publish, release,
  create a PR, or remove worktrees unless the user requests it.
- The obsolete ignored `emdash2/.scratchpad/` material is outside normal work;
  do not inspect it unless the user explicitly requests historical recovery.
