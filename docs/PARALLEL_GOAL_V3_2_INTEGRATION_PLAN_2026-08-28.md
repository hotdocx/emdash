# Parallel Goal v3.2 Integration Plan — 2026-08-28

Date: 2026-08-28

Status: complete; direct-parent merge and local-main fast-forward verified

Branch: `integration/v3.2-monads-products-profiles`

Worktree: `/home/user1/emdash1-integration-products-profiles-v3.2`

## Objective

Integrate the completed monad/product/terminal computation line and the
completed cubical/functor-property-profile line into one locally validated
history, then fast-forward local `main` in the historical project worktree
`/home/user1/emdash1`. Preserve both completed tips as the merge commit's
direct parents and preserve their source branches and worktrees unchanged.

This is an integration and authority-synchronization task. It does not reopen
the accepted mathematical designs of either parent unless their combination
exposes a concrete subject-reduction, normalization, typing, or documentation
contradiction.

## Exact Inputs And Topology

| Role | Branch | Exact tip |
| --- | --- | --- |
| Common baseline and local `main` before integration | `main` | `689f41c057f5eeee5fd82486fcad79acd136bdfa` |
| First/direct parent | `goal/monad-comonad-computation-v3.2` | `ba9e9caca980fcfbb24af8ac11928bcaf53a55cf` |
| Second/direct parent | `goal/functor-property-profiles-v3.2` | `ae43da9fea1e8eb231d5a1ccadff2b2169c01aa7` |

Both completed tips have the baseline as their exact merge base. The first is
eight commits ahead and the second is fifty-nine commits ahead. Every local
branch not already contained in `main` is contained in one of these two tips.
The detached experiment `fc98d670f95ca0c52d1bdcc5d1bb3b3b1bbf803d`
is outside both histories and is explicitly excluded.

The integration worktree was created directly at the first parent. The second
tip was merged with `--no-ff --no-commit` and `merge.conflictStyle=zdiff3`.
No preliminary integration commit is permitted: `HEAD` and `MERGE_HEAD` must
remain the two exact completed tips until the validated merge commit is made.

## Authorization And Exclusions

The user authorizes this dedicated local branch/worktree, conflict resolution,
proportional validation, one direct-parent local merge commit, and an
`--ff-only` advance of local `main`. The task does not authorize a push,
publication, release, pull request, rebase, amend, squash, reset, history
rewrite, branch deletion, worktree removal, or cleanup of detached/prunable
worktrees.

The original goal branches and worktrees are immutable integration inputs.
Generated dependency trees, ignored probes/logs, and assembled release output
must not enter the merge commit.

## Preflight Evidence

- All three relevant starting worktrees were clean, with staged and unstaged
  diffs empty.
- Both frozen leaf kernels passed bounded quiet checks before integration.
- `git diff --check` passed for both parent ranges.
- The branches overlap in eleven paths. The actual merge conflicts are
  restricted to authority/index/status text, the default check registry, and
  generated catalog/health reports.
- `emdash3_2.lp`, `emdash3_2_checks.lp`, Foundations, canonical syntax, and
  `check_metrics.py` merged textually without conflicts; their automatic merge
  still requires semantic and registry validation.

## Conflict And Ownership Policy

| Surface | Resolution owner |
| --- | --- |
| `emdash2/AGENTS.md` | Manually synthesize both authority additions, with one coherent numbered source map and no stale either-parent exclusivity claim. |
| `emdash2/reports/INDEX.md` | Retain both completed plan families and describe their current status accurately. |
| Current status/SOP | Retain both architectural summaries and consolidate the date/current evidence only after validation. |
| `emdash2/scripts/check.sh` | Form the ordered union of both parents' registered source modules and preserve the shared tail exactly once. |
| Assertion catalog | Do not hand-merge line-numbered entries; regenerate through `generate_check_catalog.py` from the resolved central checks. |
| Health report | Do not combine incompatible snapshots/timings. Regenerate an honest current source-metrics snapshot with checks explicitly skipped unless broader checking is separately justified. |

Every automatically merged semantic or registry file must be inspected against
both parents. In particular, the relaxed double-`Op_transf` involution from the
first parent must be checked together with the second parent's additions, and
both parents' new source entries must survive in `check.sh` and
`check_metrics.py`. Their pre-existing intentional registry asymmetry is not an
integration defect and remains unchanged.

## Integration Findings And Decisions

- The kernel and central diagnostic additions are disjoint at the textual
  level. Relative to the functor-property parent, the first parent's generalized
  double-`Op_transf` rule reduces the kernel inventory from `1131/159` to
  `1116/159`. All 15 removed critical-pair reports are at the `Op_transf` head
  (`30` to `15`); no new warning family appears, and combined typed checks pass.
- The profiles tip itself contained one missed downstream regression in
  `emdash3_2_dependent_simplex_ordinal_filler.lp`: three ordinary join-reindex
  endpoints used the evidence-retaining `strict_functor` view after the
  property migration, while their owner and `selected_face_func` consume
  `strict_functor_underlying`. The unchanged parent file fails the focused
  check. The integration correction uses the package projection at those
  three endpoints, adds no rule or unifier, and makes the owner and dependent
  reviewer chain green.
- Generated catalog and health conflicts were discarded as incompatible
  snapshots and regenerated through their owners. The current catalog has
  2,323 checks in 114 areas with no legacy or unclassified entries. Health is
  an explicit no-check snapshot over 324 targets, not a fabricated union of
  either parent's timing evidence.
- Three imported profile plans had recovery fields misnamed, empty on their
  header line, or beyond the linter's 40-line window. Their provenance values
  were preserved while the standard header keys/placement were repaired.

## Validation Boundary

Follow the standing scoped-validation instruction: exercise every changed or
new Lambdapi owner and reviewer from the two parent ranges, not every unrelated
registered target. Keep every Lambdapi target bounded to 90 seconds.

Required gates are:

1. merged `emdash3_2.lp` and `emdash3_2_checks.lp`;
2. every changed/new source module and reviewer example contributed by either
   parent, batched by feature family;
3. warning-enabled inventories for the merged kernel and affected rule-bearing
   owners, compared with the recorded parent boundaries and classified rather
   than treated as an automatic veto;
4. strict LHS audits for all changed rule-bearing sources;
5. regenerated strict assertion catalog with zero legacy or unclassified
   checks;
6. source-TOC, active-reference, report-header, shell/Python, registry, and
   exact-diff hygiene;
7. the affected book source/evidence check;
8. a regenerated no-check health report followed by its freshness check.

Repository-wide `make check`, `make examples`, `make health`, `make ci`, and
root `check:all` are not default gates. Escalate only if focused evidence
exposes an interaction whose classification requires a wider run.

## Execution Ledger

| Row | State | Deliverable and evidence |
| --- | --- | --- |
| `INT-00` | complete | Exact tips, merge base, branch reachability, clean worktrees, archive health, and bounded parent-kernel baselines verified. |
| `INT-01` | complete | Fresh integration worktree bootstrapped at exact first parent; exact second parent merged with `--no-ff --no-commit`; merge remains open. |
| `INT-02` | complete | Six coordination/generated conflicts resolved; 148-entry authority map and both current-plan families retained; catalog/health regenerated; automatic kernel/check/Foundations/syntax/metrics merges audited; inherited ordinal-filler regression corrected at the ordinary package projection. |
| `INT-03` | complete | Proportional combined validation is green through kernel, central diagnostics, all changed owners/reviewers, warnings, strict audits, catalog, health freshness, book, focused tooling, and final authority/diff rechecks. |
| `INT-04` | complete | The exact staged tree excludes dependency/build artifacts and creates one merge commit whose direct parents are the two frozen tips. |
| `INT-05` | complete | Clean local `main` is advanced with `--ff-only`; both source tips are ancestors and the main/integration trees agree. |

## Validation Evidence

- quiet exit 0 for the merged kernel and all 2,323 central diagnostics;
- quiet exit 0 for all 30 changed profile source owners and all 36 changed
  reviewer examples from both parents;
- exact warning inventories: kernel `1116/159`, monads `1139/159`, products
  `1179/169`, terminal objects `1123/161`; every other changed rule-bearing
  owner warning-checks with strict parser success;
- strict LHS audit: zero unreviewed findings in the kernel and all eleven
  changed rule-bearing extensions;
- strict catalog: 2,323 checks, 114 mapped areas, zero legacy and zero
  unclassified checks;
- no-check health freshness over 324 targets, source snapshot
  `08bfc957fc9c66f87ee0773cc36db9365a13c5c47df3029ea8cb7c6f4c14f9fa`
  and content snapshot
  `6c9031879e6022fe4040fae0143e9f1065e3da4e351df1dcfbe8a231203f98f6`;
- book check green with 159/159 evidence claims and 2,916 math spans; and
- 44 focused Python tests, five document-registry tests, source TOC, active
  references, report headers, shell syntax, Python compilation, and generated
  catalog checks green.

## Completion Definition

Completion requires a conflict-free combined tree; all scoped validation green
or any accepted diagnostic explicitly recorded; synchronized generated and
authority surfaces; one reviewed merge commit with the two exact tips as
direct parents; local `main` fast-forwarded to that commit; source branches and
worktrees unchanged; and no excluded external, destructive, publication, or
cleanup operation.
