# m— / emdash

`emdash` is a Lambdapi specification for functorial programming and a future
programming language/proof assistant for strict and lax omega-categories,
omega-functors, omega-transformations (“transfors”), directed families, and
dependent categorical constructions.

The computational style is inspired by Kosta Došen’s cut elimination in
categories: rewrite rules select useful runtime normal forms, while narrowly
typed unification rules relate alternative proof-time presentations when no
runtime orientation is intended.

The active development is v3.2 and remains experimental.

## Current Scope

The checked kernel currently includes:

- iterated hom-categories, ordinary functors, transfors, products, evaluation,
  curry/uncurry infrastructure, and adjunction triangles;
- directed Cat-valued families, natural/displayed functors and transfors,
  Sigma total categories, section/Pi categories, dependent homs, and fibre
  transport;
- equality/path categories, type equivalence, ordinary and omega-categorical
  equivalence staging, and explicit univalence capabilities;
- covariant/contravariant hom actions and the rigid simultaneous `Hom_*`
  action used by the unit hom profunctor;
- Cat-valued profunctors, reindexing, tensor, implication, computational
  comparison, weighted-limit/colimit staging, and adjunction mates;
- a primitive directed join slice, synthetic PathOut/path induction, and a
  reviewer-facing Eckmann–Hilton computation.

These are kernel and architecture milestones, not a finalized surface parser
or a completed foundational theory.

## Authorities And Layout

- `emdash3_2.lp`: active v3.2 kernel implementation.
- `emdash3_2_checks.lp`: executable diagnostic/regression suite.
- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`:
  current architecture and development SOP.
- `reports/EMDASH_FOUNDATIONS.md`: mathematical reading guide.
- `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`:
  notation authority for comments, examples, and future parser work.
- `reports/INDEX.md`: report lifecycle and task-specific plan map.
- `reports/REPORT_EMDASH_CHECK_CATALOG.md`: generated reviewer map of checks.
- `reports/REPORT_EMDASH_HEALTH.md`: generated validation/source metrics.
- `examples/`: small reviewer-facing milestones.
- `docs/`: local Lambdapi syntax, command, query, pattern, and tactic notes.
- `lambdapi-examples/`: upstream-style syntax and proof examples.
- `scripts/`: checking, probing, warning, decision-tree, catalog, search, and
  maintenance utilities.
- `print/`: paper/Markdown renderer and Arrowgram validation support.

Obsolete v2/v3.1 material is retired under ignored `.scratchpad/` directories
and is not part of normal development. Use the active reports rather than
historical files unless explicitly doing archaeology.

## Quick Start

Prerequisite: `lambdapi` on `PATH`. The current environment is tested with
development build `3.0.0-90-gdb4f780`; this is an environment record, not a
hard CI version gate.

```bash
make check                 # active kernel and diagnostics
make examples              # reviewer milestones
make ci                    # local handoff gate
make check-warnings        # warning-enabled kernel check
make warning-summary       # compact warning inventory + raw log
make audit-rules           # strict inferred-LHS-slot audit
make catalog               # regenerate the check catalog
make toc                   # verify header/source heading equality
make health                # refresh generated health metrics
```

During rewrite/unification development, keep checks bounded:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
timeout 20s lambdapi check emdash3_2.lp
```

If a quiet run does not localize an interaction:

```bash
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_TYPECHECK_TIMEOUT=20s make check
EMDASH_LAMBDAPI_FLAGS='--debug=u' scripts/probe.sh tmp/probes/name.lp
```

## Development Loop

For a nontrivial rule or unification change:

1. locate the semantic owner and nearby projection ladder with `rg`;
2. place the candidate in a temporary full-file copy at its intended owning
   position;
3. add a focused assertion exercising the intended runtime conversion or typed
   proof-time comparison;
4. run `scripts/probe.sh tmp/probes/name.lp` with a short timeout;
5. compare warning-enabled behavior when the change can affect overlaps;
6. promote the smallest semantically correct rule/projection and run
   `make check`;
7. update diagnostics/catalog and run `make ci` before handoff.

The detailed policies for inferred LHS slots, outer-eliminator/inner-cut
patterns, runtime versus proof-time ownership, generic `fapp*`/`tapp*`
ownership, stable projection heads, and identity normal forms live in the
current SOP report. `AGENTS.md` contains the mandatory condensed workflow.

## Useful MathOps Commands

```bash
scripts/probe.sh tmp/probes/name.lp
scripts/explain_failure.py logs/typecheck.log
scripts/decision_tree.sh fapp1_func
scripts/decision_tree.sh --png /tmp/fapp1.png fapp1_func
scripts/lambdapi_search.sh 'type >= Prof_imply_cov'
python3 scripts/audit_rule_lhs.py --show-kept
python3 scripts/arxiv_search.py --query 'cat:math.CT AND abs:"omega category"'
```

Watch mode:

```bash
make watch
tail -f logs/typecheck.log
```

Logs are retained for diagnosis and are pruned only on explicit request:

```bash
make prune-logs
EMDASH_LOG_KEEP_DAYS=7 make prune-logs
```

## Check And Documentation Maintenance

- Executable assertions belong in `emdash3_2_checks.lp`; keep the generated
  catalog fresh with `make catalog`.
- Add mathematical formulas and ownership notes adjacent to semantic symbols
  and nontrivial rule families in `emdash3_2.lp`.
- Use the canonical syntax report for comment/example notation.
- Add new reports to `reports/INDEX.md` and include the required plan metadata.
- Refresh `make health` after meaningful architecture or check changes.
- Do not treat warning counts as an automatic veto; use warning locations and
  term heads to classify concrete overlap families.

## Infinity Codex Recovery

Trusted project hooks archive completed main-agent final responses under
ignored `tmp/ai-responses/`. The archive contains recovery evidence, not
current instructions. Current code/SOP and the active task plan always take
precedence.

```bash
python3 scripts/infinity_codex.py list --limit 5
python3 scripts/infinity_codex.py latest-path
python3 scripts/infinity_codex.py show LOGICAL_ID
python3 scripts/infinity_codex.py verify
```

The hook does not archive user prompts, commentary, tool calls, or subagent
output. See the indexed Infinity Codex implementation report for the complete
recovery and retention policy.

## Print Pipeline

Run from this directory:

```bash
npm run install:print
npm run dev
npm run validate:paper
npm run check:render
```
