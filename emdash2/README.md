Our goal is to write a Lambdapi specification for a programming language (and proof assistant) for ω-categories (strict/lax), ω-functors, ω-transformations (“transfors”), and related dependent-type structures (fibrations, comma/arrow categories).

The proof assistant is inspired by the functorial programming approach of Kosta Došen, using Lambdapi rewrite and unification rules for normalization.

The proof assistant is called `m—` (read “emdash”).

## Layout
- `emdash2.lp`: ω-category-oriented development (v2, second iteration).
- `emdash3_2.lp`: active v3.2 directed-family mixed-variance development.
- `reports/REPORT_EMDASH2_CONSOLIDATED.md`: current v2 reference report.
- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`: current
  v3.2 status and rewrite/debugging SOP.
- `reports/REPORT_EMDASH_V3_2_SYNTHETIC_PATH_INDUCTION_CONSOLIDATED_PLAN_AND_STATUS_2026-05-31.md`:
  active consolidated synthetic/telescope path-induction plan and status for
  v3.2.
- Older path-induction plan/report files are superseded historical context and
  are no longer the forward plan.
- `lambdapi.pkg`: package config for Lambdapi.
- `docs/`: local copies of key Lambdapi documentation snippets (commands/syntax/queries/patterns).
- `print/`: project-local paper renderer and Arrowgram validation tools.

## Quick start
Prereq: `lambdapi` on PATH (tested with `lambdapi 3.0.0`).

- Check active Lambdapi files: `make check`
- Check just v3.2: `lambdapi check -w emdash3_2.lp`
- Timeout (recommended during early development): `EMDASH_TYPECHECK_TIMEOUT=60s make check`

## Watch mode (auto typecheck on save)
- Start a polling watcher: `make watch` (logs to `logs/typecheck.log`).
- Tail the log in another terminal: `tail -f logs/typecheck.log`.
- One-shot check: `python3 scripts/watch_typecheck.py --once`.
- Tuning: `python3 scripts/watch_typecheck.py --interval 0.2` / `--no-clear`.
- Background: `nohup make watch >/dev/null 2>&1 &` then `tail -f logs/typecheck.log`.

## Probe-first rewrite development
- Before adding a nontrivial rewrite rule to `emdash3_2.lp`, probe it in a
  temporary copy such as `tmp_rule_probe.lp`, then run
  `timeout 30s lambdapi check -w tmp_rule_probe.lp`.
- Add at least one focused `assert` exercising the intended normal form in the
  probe. A rule that typechecks but does not prove the assertion is not ready.
- If a probe times out, treat that as evidence about rule placement or LHS
  shape. Try a smaller stable-head rule, omit brittle implicit arguments, or
  move the rule later only if there is a concrete assertion showing why it is
  needed.
- Keep inferred source/target categories, endpoint families, and similar
  reconstructible arguments implicit on rule LHSs unless they are the actual
  discriminator. In particular, avoid explicit compound or reducible expressions
  in implicit-argument positions on rule LHSs.
- During debugging, keep inferred arguments explicit when that makes errors and
  constraints easier to read. Before finalizing, clean up redundant explicit
  arguments after a bounded check proves Lambdapi can infer them reliably.
- Do not add unification helpers for notation-only heads just to make surface
  syntax elaborate. If a helper would imply injectivity that is not semantically
  valid, keep it only as a temporary probe and remove it before final cleanup.
- To audit whether an existing rule is actually used, combine static search
  with a temporary-removal probe: copy `emdash3_2.lp`, remove only that rule,
  run a bounded `lambdapi check`, and inspect the first failing rule/assertion.
  Record the downstream dependency in the implementation report before deleting
  the temporary copy.
- Do not keep temporary probe files in the workspace. Move successful rules and
  their assertions into `emdash3_2.lp`, and document failed probes in the active
  implementation report when they influence the design.
- Prefer semantic definitions before introducing new stable heads. If a semantic
  construction fails to compute, first check for missing projection rules and for
  brittle explicit source/target slots.
- Use stable heads only for real projection, discrimination, or performance
  boundaries. Good stable heads are often projections from a more internalized
  construction, not substitutes for that construction.
- For Kosta Dosen-style cut-elimination, prefer reusable precomposition or
  postcomposition action heads over one-off heads that hide a raw composite. For
  example, when the desired normal form is `g o f -> fapp0(precompose_by f) g`,
  do not reuse a helper whose application rule expands in the opposite
  direction unless a focused probe shows the critical pairs are harmless. See
  `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`.
- In explicit `fapp0` source/target arguments, prefer canonical normal forms
  such as `Hom_cat ...` and `Functord_cat ...` over reducible readability
  wrappers such as `Fibre_cat (DefinedAlias ...) k`. The wrapper may compute
  alone but still trigger expensive conversion in nested assertions.
- Keep readable helper aliases routed through the named semantic constructor;
  avoid duplicating the same semantic body in multiple helper definitions.
- Treat identities as a family of normal forms, not one syntactic shape. A
  plain `@id` may reduce to specialized heads such as `id_func`, `id_funcd`, or
  constructor-specific identities before a consumer rule sees it. When a
  canonical/cartesian triangle is expected, prefer a narrow typed bridge or
  consumer-local simulation rule for that endpoint over broad global identity
  rewrites.
- Do not stop at object-level formulas when implementing internalized
  infrastructure. Check that arrow actions and projections compute at the level
  later packages need.
- Distinguish capped action `fapp1_fapp0 F p` from full hom-action
  `fapp1_func F a b`. A missing capped rule can block a valid semantic route,
  but capped object-level helpers should not replace full synthetic action.
- Keep theorem-style `assert`/`#check` statements near the symbols and comments
  that explain their mathematical formula. Reserve diagnostic sections for
  temporary normalization probes and regression checks.

## Print pipeline
Run these from this folder (`emdash2/`), independent of the parent repo workspace:

- Install print deps: `npm run install:print`
- Preview paper: `npm run dev`
- Validate diagrams/charts: `npm run validate:paper`
- Full print render check: `npm run check:render`

## Notes
- Alternative/related approaches exist in ignored `.scratchpad/` backups. Retired v3 material is under `.scratchpad/backup/2026-05-15_v3_retirement/`.
- The retired v3.1 baseline and superseded HOM/FAM/PI/CONST plan/report are in
  `.scratchpad/retired/2026-05-26_v3_1_hom_fam_pi_const/` for explicit
  archaeology only.
- Retired v2 surface-syntax notes, old email copy, and stale paper stubs are archived under `.scratchpad/backup/2026-05-15_project_docs_retirement/`.
- If typechecking takes longer than ~1 minute, treat it as a bug signal (often a rewrite/unif loop or explosion). The default `make check` runs with a timeout via `scripts/check.sh`; increase it only when you intentionally accept longer runs.
