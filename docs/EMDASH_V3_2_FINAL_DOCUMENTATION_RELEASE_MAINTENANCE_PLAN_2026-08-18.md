# Emdash v3.2 Final Documentation And Release Maintenance Plan

Date: 2026-08-18 (America/Toronto)

Plan-ID: `EMDASH-V3.2-FINAL-DOCS-RELEASE-MAINT-2026-08-18`

Status: **active bounded documentation, integration, and deployment
maintenance**. `MAINT-00`, `MAINT-DOC-1`, and `MAINT-EMAIL-2` are complete;
`MAINT-VERIFY-3` is complete and `MAINT-INTEGRATE-4` is active.

Branch: `goal/emdash-v3.2-final-maintenance`

Worktree: `/home/user1/emdash1-book-groupoidal-v3.2`

Baseline: `fee3bf5ccf008769cb0b98b84d20f44c5ce4f705`

Depends-On:

- the completed 0.5 book goal in
  `EMDASH_BOOK_V3_2_GROUPOIDAL_REALIZATION_EXPANSION_PLAN_2026-08-18.md`;
- active Lambdapi v3.2 sources, Foundations, canonical syntax, and current
  SOP;
- the completed TypeScript proof-assistant/product plans routed by
  `TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`; and
- the repository Git/checkpoint workflow in
  `PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`.

Side-Task-Ledger: `MAINT-00`, `MAINT-DOC-1`, `MAINT-EMAIL-2`,
`MAINT-VERIFY-3`, `MAINT-INTEGRATE-4`, `MAINT-PAGES-5`, and `MAINT-CLOSE-6`

## 1. Objective

Close the remaining documentation and distribution gap after the locally
released emdash book 0.5 development edition. Consolidate only genuinely
stale reader/maintainer authorities, update both external-email technical
appendices, preserve completed historical ledgers, then integrate the complete
cumulative branch into `main`, push it to GitHub, and verify the triggered
GitHub Pages deployment.

This is maintenance, not a new mathematical or TypeScript semantic tranche.

## 2. Authorization And Exclusions

The user explicitly authorized:

- a dedicated maintenance branch and local checkpoints;
- documentation and marketing-appendix edits;
- a fast-forward integration into `main` when ancestry proves it valid;
- push to GitHub; and
- verification of the resulting GitHub Pages deployment.

This authorization does not include force push, rebase, history rewriting,
tag creation, PR creation, branch/worktree deletion, npm publication, Zenodo
mutation, or an unrelated deployment. Do not run long repository/kernel
aggregates unless a changed shared contract makes omission a real blocker.

## 3. Baseline And Git Audit

The maintenance branch starts from the clean book closeout `fee3bf5`. A fresh
fetch showed:

- local and remote `main` both at `86042df`;
- `main` has zero unique commits and is 88 commits behind `fee3bf5`;
- every relevant completed TypeScript, records/classes, adjunction,
  presheaves/sites/schemes, truncation, Circle, groupoidification, and Gray
  goal tip is ancestral to `fee3bf5`; and
- the completed line can therefore be integrated by a genuine fast-forward,
  provided `main` remains unchanged and its worktree is clean at integration
  time.

The actual `main` worktree is
`/home/user1/emdash1-release-v0.2.0`. The historical default directory
`/home/user1/emdash1` presently owns
`goal/typescript-emdash-classes-v1`; it must not be treated as `main` merely
because of its path.

The Pages workflow `.github/workflows/pages.yml` triggers on a push to `main`
that changes either promoted PDF. It builds `emdash-template` and deploys its
artifact through GitHub Pages.

## 4. Documentation Audit Decisions

### Edit now

1. `emdash2/reports/EMDASH_FOUNDATIONS.md`
   - extend the opening current-module inventory through the selected Gray
     right closure/interchanger;
   - rename the Circle/groupoidal section so its heading matches its now-
     generic contents;
   - do not duplicate the book or add release chronology.
2. `docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`
   - add one short current mathematical/book boundary at the top;
   - make clear that generic groupoidification/Gray are authoritative
     Lambdapi results but are not thereby transferred into the bounded
     TypeScript profile.
3. `emdash2/tmp/EMAIL.md`
   - update the longer abstract from three applications to four mathematical
     threads;
   - add a technical section on groupoidal realization, Circle/Integer,
     generic free inversion, and selected Gray interchange;
   - add a compact corresponding passage to the shorter appendix;
   - preserve the established external-reviewer notation and exact nonclaims.

### Already synchronized; inspect but do not churn

- `README.md` and `emdash2/README.md` now route to the 0.5 book and summarize
  generic groupoidification/Gray with exact boundaries.
- `REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md` already inventories
  the active owners and records the promoted 0.5 artifact.
- `REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md` already owns
  strict-profile, Gray, interval, generic groupoidification, and truncation
  notation.
- root and nested `AGENTS.md` already contain the current authority order and
  module inventory.
- `PERSISTENT_GOAL_GIT_EXPERIMENTATION.md` already states the correct
  authorization, checkpoint, resume, integration, and cleanup boundaries.
- the TypeScript master, DTT/LF, and scale plans are completed/preserved
  historical ledgers; their old scoped deferrals must not be rewritten as if
  they were current global claims.

## 5. Email Architecture

The longer appendix should expose four mathematical threads:

1. directed dependent hom and synthetic arrow induction;
2. WalkingEnd/Natural-number normalization;
3. invertibility sieves, generated topology, and direct Cat-valued
   sheafification; and
4. the path/groupoidal return: Circle/Integer, category-indexed
   groupoidification, and the profiled Gray walking interchanger.

The fourth thread must state the checked mapping property

```text
Hom_Grpd(Groupoidify(C),G) ≃_omega Functor(C,Path(G))
```

as target-side and whole, while deferring source action and the packaged
adjunction. Gray is one selected strict-object/lax-arrow right closure with a
derived nonidentity interchanger, not the full Crans--Gray monoidal theory.

The shorter appendix should add only a compact Circle/free-inversion/Gray
passage after WalkingEnd/Nat; it should retain its intentionally abbreviated
arrow-induction notation.

## 6. Validation Policy

Documentation tranches require:

- exact diff and `git diff --check`;
- `lint_report_headers.py` and `lint_active_refs.sh` when reports change;
- book/article source-to-promoted byte comparisons, because no artifact owner
  is being edited;
- lexical checks that active descriptions no longer make generic
  groupoidification prospective; and
- no Lambdapi, root TypeScript, browser, book, or repository aggregate merely
  for prose edits.

Before integration:

- fetch `origin` again;
- require the maintenance tip to descend from both `main` and the completed
  book tip;
- require the dedicated branch and `main` worktrees to be clean;
- require `main...maintenance` to have zero left-only commits;
- stage/commit only reviewed plan-owned paths; and
- record exact artifact hashes carried into `main`.

After push:

- verify `origin/main` equals local `main` and the maintenance tip;
- inspect the triggered `pages.yml` run with `gh` until terminal;
- require both build and deploy jobs to succeed; and
- verify the public reviewer URL responds and exposes the updated book and
  article assets.

## 7. Execution Ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `MAINT-00` | complete | Audited worktrees, remote/main ancestry, Pages trigger, foundational/SOP documents, TypeScript plans, READMEs, and both email appendices; selected only three authored targets for content edits. |
| `MAINT-DOC-1` | complete | Foundations now names groupoidal realization at the section boundary and includes path pseudo-laxity plus the profiled Gray slice in its opening active-module inventory. The TypeScript “Start Here” handoff now states the current mathematical/book boundary while explicitly withholding automatic TypeScript-profile expansion. Canonical syntax, current SOP, both AGENTS files, persistent-goal SOP, and completed TypeScript plans were inspected and intentionally left unchanged. |
| `MAINT-EMAIL-2` | complete | The longer abstract now has four mathematical threads and a standalone groupoidal-realization/Gray section; the shorter appendix has a compact corresponding passage. Both distinguish Path from Groupoidify, state Circle computation and the target-side whole mapping equivalence, derive the profiled interchanger from whole laxity, and defer source action/adjunction/full Gray monoidality. |
| `MAINT-VERIFY-3` | complete | Exact diff/fence audit, `git diff --check`, report-header lint, active-reference lint, and the centralized Infinity archive verification pass. All four checked book/article owners remain byte-equal to their tracked distributions; no artifact or semantic owner changed. |
| `MAINT-INTEGRATE-4` | active | Re-fetch, prove zero divergence, fast-forward `main` in its actual worktree, and push `origin/main`. |
| `MAINT-PAGES-5` | pending | Follow the triggered Pages workflow to success and verify the deployed reviewer/assets. |
| `MAINT-CLOSE-6` | pending | Record commits, hashes, remote/deployment evidence, clean states, and complete the persistent goal without deleting branches/worktrees. |

### 7.1 Documentation Implementation Record — 2026-08-18

The consolidation changes exactly three authored content targets plus this
plan:

- Foundations now names groupoidal realization rather than the earlier
  representative-only closure and includes path pseudo-laxity/Gray in its
  current-module overview;
- the TypeScript handoff advertises the current mathematical/book boundary
  while preserving the reviewed-transfer gate; and
- `EMAIL.md` grows from 3,171 to 3,857 words across its intentionally long and
  short variants, adding 686 words of groupoidal/free-inversion/Gray material
  with the same external-reviewer notation.

No edit was made to canonical syntax, the current mathematical SOP, either
AGENTS file, the persistent-goal Git SOP, or the completed TypeScript master,
DTT/LF, and scale ledgers. Their audited claims are already scoped correctly.

Focused validation is green:

```text
git diff --check: passed
report header lint: 18 current plans passed
active-reference lint: passed
central Infinity archive: 718 responses verified
EMAIL.md code fences: 150 (balanced)
TypeScript handoff code fences: 16 (balanced)
book Markdown/PDF owner comparisons: equal
article Markdown/PDF owner comparisons: equal
```

## 8. Completion Definition

This maintenance goal is complete only when:

- each ledger row is complete or explicitly deferred behind a concrete
  external prerequisite;
- Foundations, TypeScript handoff, public READMEs/status, and `EMAIL.md` agree
  on the checked mathematical/product boundary;
- already-current SOP/canonical/historical documents remain unchurned;
- all focused documentation gates pass;
- `main`, `origin/main`, and the maintenance tip identify the same integrated
  commit;
- the triggered GitHub Pages run succeeds and the public site is reachable;
- all involved worktrees are clean; and
- no excluded destructive, publication, tag, PR, npm, or Zenodo operation was
  performed.
