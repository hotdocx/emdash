Our goal is to write a Lambdapi specification for a programming language (and proof assistant) for ω-categories (strict/lax), ω-functors, ω-transformations (“transfors”), and related dependent-type structures (fibrations, comma/arrow categories).

The proof assistant is inspired by the functorial programming approach of Kosta Došen, using Lambdapi rewrite and unification rules for normalization.

The proof assistant is called `m—` (read “emdash”).

## Layout
- `emdash3_2.lp`: active v3.2 directed-family mixed-variance development.
- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`: current
  v3.2 status and rewrite/debugging SOP.
- `reports/EMDASH_FOUNDATIONS.md`: mathematician-facing reading guide for the
  current v3.2 foundations.
- `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`:
  current notation authority for comments, examples, and future parser work.
- `reports/REPORT_EMDASH_V3_2_FUNCTOR_STRUCTURAL_LOGIC_PRELIM_PLAN_2026-06-04.md`:
  active proposed plan for structural functor logic
  (weakening/exchange/contraction and displayed follow-ups).
- `reports/REPORT_EMDASH_V3_2_PI_ALONG_FUNCTOR_IMPLEMENTATION_PLAN_2026-06-11.md`:
  active proposed plan for dependent products along functors (`Pi_f`) and
  comma-category infrastructure.
- `reports/REPORT_EMDASH_V3_2_PROFUNCTOR_WEIGHTED_LIMITS_PRELIM_PLAN_2026-06-17.md`:
  active implementation plan and log for Cat-valued profunctors, tensor and
  internal hom, weighted limits, duality, and the directed-inductive stress
  test.
- `reports/REPORT_EMDASH_V3_2_NOTATION_MIGRATION_AND_REORG_IMPLEMENTATION_PLAN_2026-06-05.md`:
  active notation/reorganization subplan.
- `reports/REPORT_EMDASH_V2_RETIREMENT_AUDIT_2026-06-16.md`: audit explaining
  why the old v2 baseline was retired and which ideas remain future design
  material.
- `reports/INDEX.md`: current report map.
- `research/literature.md`: MathOps literature-discovery workflow.
- Older v3/v3.2 feature reports have been consolidated into the current SOP
  and foundations reports, then archived under `.scratchpad/retired/`.
- `lambdapi.pkg`: package config for Lambdapi.
- `docs/`: local copies of key Lambdapi documentation snippets (commands/syntax/queries/patterns).
- `print/`: project-local paper renderer and Arrowgram validation tools.

## Quick start
Prereq: `lambdapi` on PATH (tested with `lambdapi 3.0.0`).

- Check active Lambdapi files: `make check`
- Check reviewer milestone examples: `make examples`
- Run local CI gate: `make ci`
- Regenerate the check catalog: `make catalog`
- Refresh the health report: `make health`
- Check just v3.2: `lambdapi check -w emdash3_2.lp`
- Timeout (recommended during early development): `EMDASH_TYPECHECK_TIMEOUT=60s make check`
- Diagnostic kernel check with Lambdapi warnings enabled:
  `make check-warnings`

## Watch mode (auto typecheck on save)
- Start a polling watcher: `make watch` (logs to `logs/typecheck.log`).
- Tail the log in another terminal: `tail -f logs/typecheck.log`.
- One-shot check: `python3 scripts/watch_typecheck.py --once`.
- Tuning: `python3 scripts/watch_typecheck.py --interval 0.2` / `--no-clear`.
- Background: `nohup make watch >/dev/null 2>&1 &` then `tail -f logs/typecheck.log`.

## MathOps utilities
- Stale active-reference lint: `./scripts/lint_active_refs.sh`.
- Check/source metrics: `python3 scripts/check_metrics.py --write-report`.
- Probe a temporary Lambdapi file with a compact failure summary:
  `scripts/probe.sh tmp/probes/name.lp`.
- Summarize an existing Lambdapi log: `scripts/explain_failure.py logs/typecheck.log`.
- Show the first warning from a warning-enabled log:
  `scripts/explain_failure.py --warning logs/typecheck.log`.
- Audit reconstructible compound terms in inferred rewrite-rule LHS slots:
  `python3 scripts/audit_rule_lhs.py`.
- Inspect rewrite compilation: `scripts/decision_tree.sh homd_`.
- arXiv/ar5iv discovery:
  `python3 scripts/arxiv_search.py --query 'cat:math.CT AND abs:"omega category"'`.
- Reviewer milestone examples live in `examples/`.

Quiet project checks use Lambdapi's `-w` flag to suppress the large existing
critical-pair warning stream. When a quiet check times out or does not identify
the interacting rule, rerun the smallest target with warnings enabled:

```bash
timeout 20s lambdapi check emdash3_2.lp
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_TYPECHECK_TIMEOUT=20s make check
EMDASH_LAMBDAPI_WARNINGS=1 scripts/probe.sh tmp/probes/name.lp
```

All project check/probe/metrics scripts also append flags from
`EMDASH_LAMBDAPI_FLAGS`, for example
`EMDASH_LAMBDAPI_FLAGS='--debug=u'`. Redirect warning/debug output to a log
when necessary.

The LHS audit is advisory. Constructor patterns such as `Op_cat`,
`Product_cat`, `Sigma_cat`, and dependent-pair endpoints may be intentional
discriminators. Replace a reported slot by `_` only after a focused probe and
bounded full check.

## Probe-first rewrite development
- Before adding a nontrivial rewrite rule to `emdash3_2.lp`, probe it in a
  temporary file such as `tmp/probes/name.lp`, then run
  `scripts/probe.sh tmp/probes/name.lp`.
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
- If a new rewrite or unification rule causes a timeout, use a warning-enabled
  run to locate the existing interacting rule. Audit that rule's inferred
  argument slots before concluding the new rule is too broad; explicit
  `fapp0`, composition, pullback, opposite, or family expressions in
  non-discriminator slots can create avoidable unification search.
- During debugging, keep inferred arguments explicit when that makes errors and
  constraints easier to read. Before finalizing, clean up redundant explicit
  arguments after a bounded check proves Lambdapi can infer them reliably.
- Do not add unification helpers for notation-only heads just to make surface
  syntax elaborate. If a helper would imply injectivity that is not semantically
  valid, keep it only as a temporary probe and remove it before final cleanup.
- To audit whether an existing rule is actually used, combine static search
  with a temporary-removal probe: copy `emdash3_2.lp`, remove only that rule,
  run `scripts/probe.sh` on the copy, and inspect the first failing
  rule/assertion.
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
- Cat-specialized semantic heads package extra structure exposed only when the
  ambient category is `Cat_cat`. For example, a generic hom-action arrow may
  have a Cat-specialized presentation as a transfor, where `tapp0_fapp0`,
  `tapp1_func`, and `tapp1_fapp0` projections become meaningful. Prefer these
  Cat heads when they keep the projection ladder readable, but document the
  generic owner and any overlap/join with it.
- Do not keep a parallel stable-head package for an action already owned by an
  internalized functor. Prefer adjacent stable projection rungs before attaching
  computation, for example
  `Product_cat_fapp1_func` -> `Product_cat_fapp1_fapp0_functord` ->
  `Product_cat_fapp1_tapp0_func`; retain higher helper names only as
  definitions/aliases of that semantic owner.
- For Kosta Dosen-style cut-elimination, prefer reusable precomposition or
  postcomposition action heads over one-off heads that hide a raw composite. For
  example, when the desired normal form is `g o f -> fapp0(precompose_by f) g`,
  do not reuse a helper whose application rule expands in the opposite
  direction unless a focused probe shows the critical pairs are harmless. See
  `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`.
- When one endpoint of a hom varies by a functor, prefer the hom-indexed family
  owner (`hom_int`, `hom_con`, or displayed `homd_int(FF)`) over a hand-built
  `comp_cat*` pipeline; this keeps pre/postcomposition under the hom-action
  projection ladder.
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
- Do not stop at pointwise formulas when implementing internalized
  infrastructure. A sketch like `A[x] = ...` is only the object law when `x`
  varies functorially; a sketch like `eta[x] = ...` is only the component law
  of a transfor. Also specify the action over `p : x -> y`, such as `A[p]` or
  `fapp1_func A`, and `eta[p]` or `tapp1_func eta`. Capped or
  constructor-specific `fapp1*`/`tapp1*` helpers may be the practical probe
  surface, but they should not hide the full arrow-action obligation.
- Distinguish capped action `fapp1_fapp0 F p` from full hom-action
  `fapp1_func F a b`. A missing capped rule can block a valid semantic route,
  but capped object-level helpers should not replace full synthetic action.
- Keep theorem-style `assert`/`#check` statements near the symbols and comments
  that explain their mathematical formula. Reserve diagnostic sections for
  temporary normalization probes and regression checks.
- For readability cleanup, distinguish four surfaces:
  rule LHSs, rule RHSs/defined bodies, theorem-style assertions, and
  diagnostic assertions. Rule LHSs should stay conservative and keep the
  stable discriminator explicit. RHSs and defined bodies may omit inferred
  arguments only after a probe shows type preservation still succeeds.
  Theorem-style assertions should prefer the mathematical formula, often
  projectionwise for products. Diagnostic assertions may remain explicit,
  especially for full `fapp1_func`/capped `fapp1_fapp0` endpoints, hidden
  fixed product factors such as `Product_cat_fapp1_tapp0_func A A' B G`, and
  product-valued hom-actions where Lambdapi otherwise reconstructs endpoints
  through large `sigma_Fst`/`sigma_Snd` terms.
- Prefer mostly horizontal formatting for simple stable-head rules after they
  have stabilized. Keep vertical layout for nested endpoint formulas, explicit
  source/target categories, and diagnostic assertions. See the layout SOP in
  `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`.
- Write declared symbol types in reduced/canonical form by default. Prefer
  `τ (Functord E D)` over unreduced equivalents such as
  `τ (@Transf K Cat_cat E D)` unless the unreduced shape is intentionally
  needed for a projection route or diagnostic assertion; document that exception
  near the symbol. Avoid adding decoded `*_TYPE` or classifier heads merely to
  shorten binders: they introduce a parallel theory layer and require matching
  reductions for every semantic specialization, such as Cat-valued and
  product-valued transfors. A decoded `TYPE` head alone also does not replace
  `Obj(...)` unification rules; that would require a classifier-level head and
  corresponding confluence checks.

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
