# Persistent Goal Git Experimentation

Date: 2026-07-23
Status: active repository-wide workflow for long-running implementation goals

## Purpose

This workflow makes long-running, mostly unsupervised Codex `/goal`
implementation recoverable and reviewable. It supplements `AGENTS.md` and the
task-specific plan; it never relaxes a package's authority order, safety rules,
or validation SOP.

A persistent goal is not by itself permission to commit, create a branch or
worktree, push, merge, publish, rewrite history, or remove a worktree. The
launch prompt or user must explicitly authorize each class of Git mutation.
The TypeScript elaborator master plan includes a prompt that authorizes a
narrow class: one dedicated local goal branch/worktree and local validated
checkpoint commits there.

## Preferred Topology

Use one dedicated branch and worktree for a long-running implementation. This
isolates dependency links, checkpoints, and temporary state from unrelated
work.

Example, only when branch/worktree creation is authorized:

```bash
git worktree add \
  ../emdash1-elaborator-goal \
  -b goal/typescript-elaborator-v3.2 \
  a06433e57cba95e7d35f8577b7c71912862c3d25
cd ../emdash1-elaborator-goal
./scripts/bootstrap-worktree.sh
```

Choose a new path and branch name after checking:

```bash
git worktree list
git branch --list
```

Never share or symlink `node_modules` between worktrees. The repository's pnpm
bootstrap already reuses the immutable package store.

If the goal begins in an already authorized dedicated branch/worktree, work
from its current descendant state. The plan's baseline is a comparison anchor,
not a command to discard checkpoints.

## Start And Resume Checklist

At the start of every goal continuation, including after context compaction:

1. read the root and nearest nested `AGENTS.md`;
2. read the task's active living plan and current authority/SOP entries;
3. inspect all worktrees, the branch, `HEAD`, and the baseline relationship;
4. inspect staged and unstaged state separately, including untracked files;
5. identify any unrelated or pre-existing work and exclude it from the slice;
6. relocate the current definitions and consumers with `rg`;
7. run the bounded baseline required by the affected package;
8. resume the one in-progress slice or select the next dependency-ready row.

Useful read-only commands:

```bash
git worktree list
git status --short --branch
git diff --stat
git diff
git diff --cached --stat
git diff --cached
git log --oneline --decorate -n 12
git merge-base --is-ancestor BASELINE_COMMIT HEAD
```

Do not continue from an archived response or summary alone. Those are recovery
evidence; current code, authorities, plan ledger, and Git state decide what is
true.

## Bounded Experiment Loop

Every implementation experiment should answer one concrete question:

```text
hypothesis
  → smallest owner-position implementation/probe
  → positive consumer
  → relevant negative or non-collapse consumer
  → bounded checks and interaction evidence
  → accept, refine, reject, or defer
  → synchronize code/tests/plan
```

Before changing architecture, record:

- the owner and expected mathematical form;
- the current authority source;
- what observation would reject the hypothesis;
- the smallest affected plan row;
- the required proportional validation.

Prefer ignored temporary probes for disposable investigation and focused
tracked tests for durable behavior. A successful isolated term is not enough:
test it at its owning position and in the first real consumer. For kernel
rules, compare warnings and complete the audits/catalog/health workflow
required by `emdash2/AGENTS.md`.

If an experiment invalidates the plan, revise the plan. Do not preserve a
failed architecture merely because it was previously scheduled.

## Local Checkpoint Commits

Create a local checkpoint only when all of the following are true:

- the launch prompt or user explicitly authorizes local commits;
- the work is on the intended dedicated goal branch;
- the tranche is bounded and internally coherent;
- its focused and proportional gates are green;
- the living plan records the result, evidence, dependencies, and next state;
- staged paths contain no unrelated or pre-existing user work;
- the exact staged diff and `git diff --cached --check` have been reviewed.

Use path-scoped staging:

```bash
git status --short
git diff -- path/to/owned-file
git add -- path/to/owned-file path/to/focused-test path/to/living-plan
git diff --cached --stat
git diff --cached
git diff --cached --check
git commit -m "elaborator: complete ELAB-X bounded slice"
```

Do not use `git add -A` in a worktree containing unrelated changes. Never
commit generated dependency trees, probe logs, temporary consumers, assembled
book output, or other files excluded by their owning workflow.

A checkpoint commit means “reviewable evidence at this point,” not “final
design.” Prefer a short chain of validated semantic checkpoints over one large
mixed commit or a checkpoint for every exploratory edit.

## Backtracking And Competing Designs

Do not use `git reset --hard`, destructive checkout, rebase, amend, force push,
or history rewriting to hide a failed experiment.

For a small mistake, make a new correcting commit. For a coherent committed
experiment that must be undone, use a reviewed follow-up revert only when its
exact target and effect are in scope. For materially competing designs, branch
or create a separate authorized worktree from the last common validated
checkpoint, then record:

- the common baseline/checkpoint;
- the hypothesis unique to each branch;
- the same comparison corpus and gates;
- the measured result and selected orientation.

Do not merge an experimental branch merely because it compiles. First record
why it wins and how the losing evidence affects the living plan.

## Dirty Work And External Changes

Existing staged, unstaged, and untracked changes belong to the user unless
proved otherwise. Preserve them and work around them.

If an authorized goal resumes with its own unfinished changes:

- reconstruct their intended plan slice from the ledger and diff;
- rerun the smallest relevant checks before building on them;
- do not checkpoint partial work under a misleading completed-slice message;
- keep staged and unstaged intent separate.

If unrelated changes overlap files required by the next slice, stop that slice,
record the overlap, and pursue independent dependency-ready work. Do not stash,
discard, or absorb the user's changes without authorization.

## Kernel Experiments

Git isolation does not make a Lambdapi rule safe. Every `emdash2/` semantic
change still follows the nested SOP:

1. locate the current owner;
2. probe a temporary full-file copy at the owning position;
3. include a positive typed consumer and relevant negative;
4. compare warnings and subject-reduction effects;
5. run rule/LHS audits;
6. promote only the smallest coherent change;
7. synchronize diagnostics, examples, catalogs, health, and reports;
8. run the required bounded and full CI gates.

A missing elaborator capability is not automatic authority to add a kernel
rewrite. Record whether the gap belongs in surface elaboration, explicit Core,
an existing theorem/comparison, or a genuinely missing owner.

## Commit, Handoff, And Completion Boundaries

Unless separately authorized, even an authorized checkpoint goal must not:

- push or force-push;
- merge into `main` or another branch;
- create a pull request;
- publish or release;
- rebase, amend, squash, or rewrite checkpoint history;
- delete branches or remove worktrees.

At each checkpoint or handoff, report:

- branch/worktree and `HEAD`;
- completed plan row and changed decision entries;
- exact validation commands/results;
- staged and unstaged state;
- remaining dependency-ready row;
- any human decision, failed probe, or external prerequisite.

The goal is complete only when every scoped plan row is implemented, rejected
with durable evidence, or explicitly deferred behind a concrete prerequisite
or human decision, and all affected authorities and final gates are
synchronized. Nearness to a token/time budget is not completion.

Cleanup is a separate operation. Leave the branch/worktree intact unless the
user explicitly requests removal after inspecting the final state.
