# emdash3 Repository Consolidation Cleanup Plan

## Summary

- Keep `emdash3_1.lp` as the canonical active v3 iteration; do not rename it
  to `emdash3.lp`.
- Retire obsolete v3 files by copying them into ignored
  `.scratchpad/backup/2026-05-15_v3_retirement/`, then removing the tracked
  originals.
- Create `reports/REPORT_EMDASH_V3_CONSOLIDATED.md` as the single tracked v3
  source of truth.
- Update repo docs and validation commands so future work points at
  `emdash3_1.lp`.

## Key Changes

- Add `reports/REPORT_EMDASH_V3_CONSOLIDATED.md`.
- Document the current architecture: directed `Fam`, `Sigma_cat`,
  mixed-variance `Functor_fam` / `Functor_mix_fam_func`, `Edge_fam`,
  `HomPresheaf_fam`, `Homd_*`, and endpoint `homd_`.
- Record rewrite/SOP lessons: stable heads, avoid reducible compounds in
  implicit LHS positions, `Transf_cat` unification helpers, and no
  reintroduction of `homd_eval_func` / `sigma_hom_fam`.
- Archive then remove tracked obsolete v3 material:
  - `emdash3.lp`
  - `PRD_EMDASH_V3_INITIAL_IDEA.md`
  - old `reports/emdash3_*` and `reports/emdash3_1_*_plan.md` draft reports.
- Also archive old current-looking reports that present retired `Homd_func`
  material as active guidance: `REPORT_EMDASH_TYPESCRIPT_ELABORATION.md` and
  `REPORT_EMDASH_LOGIC_DEV_3.md`.
- Update `README.md`, `AGENTS.md`, `Makefile`, and `scripts/check.sh` so the
  active v3 file is `emdash3_1.lp`.
- Lightly clean `emdash3_1.lp`: update the header, avoid stale
  `sigma_hom_fam` wording, and replace the large commented-out generic
  Sigma/Pi helper sketch with a short TODO that points to the consolidated
  backlog.

## Test Plan

- `lambdapi check -w emdash3_1.lp`
- `lambdapi check -w emdash2.lp`
- `EMDASH_TYPECHECK_TIMEOUT=60s make check`
- `git diff --check`
- `rg -n "emdash3\\.lp" README.md AGENTS.md reports emdash3_1.lp`
- `rg -n "homd_eval_func|Homd_func|sigma_hom_fam|PredPi_catd|Catdd" README.md AGENTS.md reports emdash3_1.lp`

Expected result: old names appear only in the consolidated report and this
cleanup plan as superseded history/backlog.

## Assumptions

- "Delete" means preserve a copy in ignored
  `.scratchpad/backup/2026-05-15_v3_retirement/`, then remove the tracked file.
- `emdash3_1.lp` remains the active filename because future iterations may use
  `emdash3_2.lp`, etc.
- The old `emdash3.lp` Catd/Catdd/PredPi code contributes historical lessons
  only; no direct symbols should be ported before retirement.
