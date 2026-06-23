# EMDASH MathOps / DevOps Implementation Plan

Date: 2026-06-16

Plan-ID: EMDASH-MATHOPS-DEVOPS-2026-06-16
Depends-On: none
Supersedes: none
Side-Task-Ledger: none
Infinity-Codex-Origin: pre-infinity-codex
Infinity-Codex-Decision-Responses: none

Status: proposed implementation plan for improving the project SOP, validation
loop, literature discovery, and reviewer-facing evidence.

## Assessment

The project is now at the right point to improve process. `emdash3_2.lp` has
become a serious kernel draft, `emdash3_2_checks.lp` is already a regression
suite, and the v2 retirement removed a major source of drift. The next
improvements should be small tooling and public-facing review surfaces around
the current single-file workflow, not a heavy build-system migration.

Useful outside models:

- arXiv has a documented Atom API with `search_query`, `id_list`, paging via
  `start`/`max_results`, and sorting by last update, submission date, or
  relevance.
- ar5iv is useful for reading arXiv papers as HTML by changing `arxiv` to
  `ar5iv`, but the arXiv PDF/source remains the authority for exact formulas.
- Mathlib's public process emphasizes linters, CI, systematic docs, human
  review, PR summaries, and technical-debt metrics.
- Alectryon is a useful model for literate proof artifacts: prose mixed with
  checked proof snippets and rendered proof/checker output.

## Highest-Value Additions

1. Add a `make ci` target.

Current `make check` is good but narrow. Add a target that runs:

```bash
./scripts/check.sh
git diff --check
./scripts/lint_active_refs.sh
python3 scripts/check_metrics.py --update-log
```

Optionally, if print dependencies are installed, keep a separate render gate:

```bash
make ci-render
```

2. Add a machine-readable check summary.

Create `scripts/check_metrics.py` to record:

- Lambdapi version;
- check duration for `emdash3_2.lp`;
- check duration for `emdash3_2_checks.lp`;
- number of `symbol`, `rule`, `unif_rule`, and `assert` commands;
- number of TODO/deferred comments;
- section line counts.

Output:

```text
logs/check-metrics.jsonl
reports/REPORT_EMDASH_HEALTH.md
```

3. Add a check catalog generator.

`emdash3_2_checks.lp` is valuable, but source-line comments drift. Move
gradually toward stable tags:

```text
// CHECK: core.path.obj
assert [A : Grpd] |- Obj (Path_cat A) == A;
```

Then a script can generate:

```text
reports/REPORT_EMDASH_CHECK_CATALOG.md
```

Grouped by section: kernel, products, Sigma, homd, displayed laxity, path
induction, adjunctions. This is one of the best external-review artifacts.

4. Add a research/literature workflow.

Create:

```text
research/
  literature.md
  notes/
scripts/arxiv_search.py
```

The arXiv helper should query the arXiv API, cache results, and emit both arXiv
and ar5iv links. Typical usage:

```bash
python3 scripts/arxiv_search.py \
  --query 'cat:math.CT AND (abs:"omega category" OR abs:"higher category")' \
  --max-results 25 \
  --sort lastUpdatedDate
```

Useful categories and keywords:

```text
cat:math.CT, cat:math.LO, cat:cs.LO, cat:cs.PL
"omega category", "weak omega category", "strict omega category"
"polygraph", "computad", "higher dimensional rewriting"
"categorical proof theory", "cut elimination", "Dosen"
"dependent type theory" AND "category theory"
"directed type theory", "displayed category", "Grothendieck construction"
```

SOP: use ar5iv for skimming/searching text; use arXiv PDF/source for exact
formulas.

5. Add reviewer-facing demos.

External reviewers should not have to read a long kernel file. Add checked
milestones:

```text
examples/
  01_path_category.lp
  02_products_eval_curry.lp
  03_sigma_transport.lp
  04_dependent_hom.lp
  05_path_induction_transitivity.lp
  06_adjunction_triangles.lp
```

Each should answer: "what meaningful theorem/computation does this file
demonstrate?" The current transitivity/composition benchmark is exactly the
kind of result to showcase.

6. Add lightweight linters.

Good candidates:

- `scripts/lint_active_refs.sh`: forbid active references to `.scratchpad`,
  retired files, and obsolete reports.
- `scripts/lint_lp_comments.py`: scan comments for obsolete syntax or
  known-danger phrases.
- `scripts/lint_rule_lhs.py`: heuristic detector for reducible expressions in
  implicit LHS slots.
- A complementary nested-cut audit should flag candidate commuting conversions
  of the form `outer_eliminator(inner_rewrite_active_head(...))`, while
  allowing explicit exceptions for constructor beta rules and designated
  projection ladders. This should remain advisory unless symbol reducibility
  can be classified reliably; warning-enabled owning-position probes remain
  the promotion authority.
- `scripts/lint_assert_tags.py`: eventually require every check to have a
  stable `CHECK:` tag.

These do not need to be perfect. They only need to catch common regressions.

## Project Reorganization

Keep `emdash3_2.lp` at root for now. Premature folder moves would create
module-path churn. Prefer:

```text
docs/
  lambdapi/        # move local Lambdapi docs here later
  mathops/         # SOPs and workflows
examples/          # reviewer-facing checked examples
research/
  literature.md
  notes/
reports/
  INDEX.md         # active report map
scripts/
logs/
```

The first folder change should be `reports/INDEX.md`, because the reports
folder is already dense. It should say which reports are active, retired, or
historical.

## Agentic AI Loop

The loop should stay lightweight during editing and become strict only at
handoff:

```text
plan/probe -> edit -> bounded check -> handoff CI -> report refresh when needed
```

Practical improvements:

- `scripts/probe.sh tmp/probes/name.lp`: runs a focused bounded check on an
  explicit probe file and writes a log.
- `scripts/explain_failure.py logs/typecheck.log`: extracts the first Lambdapi
  error with nearby source context.
- `scripts/decision_tree.sh SYMBOL`: wraps `lambdapi decision-tree` for rewrite
  debugging.
- `logs/session-notes.md`: optional rolling notes for failed probes worth
  remembering.
- `make catalog` is non-strict so it remains useful while new checks are being
  sorted; `make ci` runs the strict freshness/classification check.

For AI work, the key is that checker output should be compact, stable, and
easy to feed into the next iteration.

## Implementation Order

1. `reports/INDEX.md`
2. `make ci` plus `scripts/lint_active_refs.sh`
3. `scripts/check_metrics.py`
4. `research/literature.md` plus `scripts/arxiv_search.py`
5. `reports/REPORT_EMDASH_CHECK_CATALOG.md` generator
6. `examples/` reviewer milestone suite

Initial implementation status:

- `reports/INDEX.md`: implemented.
- `make ci`, stale-reference lint, and check metrics: implemented.
- `research/literature.md` and `scripts/arxiv_search.py`: implemented.
- `reports/REPORT_EMDASH_CHECK_CATALOG.md` generator: implemented.
- `examples/` reviewer milestone suite: implemented.
- Examples are included in `scripts/check_metrics.py` and
  `reports/REPORT_EMDASH_HEALTH.md`: implemented.
- Focused checker-loop helpers `scripts/probe.sh`,
  `scripts/explain_failure.py`, and `scripts/decision_tree.sh`: implemented.
- Inferred-slot LHS auditing is implemented as `scripts/audit_rule_lhs.py`.
  Automatic classification of outer-eliminator/inner-cut commuting
  conversions remains a possible tooling extension; the active SOP currently
  requires manual review plus a warning-enabled full-file probe.
- Friction review update: `make ci` now uses compact metrics output, while
  `make catalog` is exploratory/non-strict and `make ci` remains strict.
- 2026-06-21 lightweight tooling review:
  - obsolete Gemini/Antigravity agent metadata is removed; `AGENTS.md`
    remains the Codex-facing instruction source with the intentionally
    embedded Lambdapi reference;
  - current Lambdapi search syntax and explicit index usage are documented,
    with `scripts/lambdapi_search.sh` as an optional normalized/type-aware
    supplement to `rg`;
  - `scripts/decision_tree.sh` suppresses unrelated warnings and can render
    PNG output through Graphviz;
  - `make warning-summary` provides an opt-in compact warning inventory while
    retaining one raw latest log;
  - `make prune-logs` provides manual cleanup and is not called by the normal
    check, probe, or CI loops;
  - the tested development build is recorded but intentionally not enforced,
    so toolchain setup cannot block exploratory mathematics.
- 2026-06-23 Infinity Codex extension:
  - a trusted repo-local `Stop` hook archives only exact main-agent final
    responses under ignored `tmp/ai-responses/`;
  - a `SessionStart` hook for resume/compaction injects recovery pointers
    without injecting archived prose;
  - immutable per-turn metadata, generated indexes, logical response IDs,
    verification, explicit pruning, and plan annotation are implemented in
    `scripts/infinity_codex.py`;
  - `make infinity-codex-test` and `make ci` validate the hook and archive;
  - the archive is deliberately independent of Codex Memories and remains
    subordinate to active code, SOPs, plans, and side-task ledgers.

This sequence improves daily development immediately, then improves research
intake, then improves external credibility.
