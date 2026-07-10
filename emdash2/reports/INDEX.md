# EMDASH Reports Index

Date: 2026-07-07

Use this file as the first stop for report discovery. The active code authority
is still `emdash3_2.lp`; reports explain status, notation, plans, and review
decisions.

## Current Orientation

- `REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`:
  current implementation status, validation workflow, rewrite-rule SOP, and
  known deferred items.
- `EMDASH_FOUNDATIONS.md`: mathematician-facing reading guide for the current
  directed-family foundations.
- `REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`: current
  notation authority for comments, examples, and future parser work.

## Current Plans

- `REPORT_EMDASH_INFINITY_CODEX_IMPLEMENTATION_PLAN_2026-06-23.md`:
  controlled local archiving of Codex final responses, compaction/resume
  recovery pointers, plan provenance, and related agentic MathOps.
- `REPORT_EMDASH_MATHOPS_DEVOPS_IMPLEMENTATION_PLAN_2026-06-16.md`:
  MathOps/DevOps/SOP improvement plan and implementation order.
- `REPORT_EMDASH_V3_2_REORGANIZATION_PLAN_2026-06-16.md`: split-ready section
  ordering plan for `emdash3_2.lp`.
- `REPORT_EMDASH_V3_2_PI_ALONG_FUNCTOR_IMPLEMENTATION_PLAN_2026-06-11.md`:
  dependent products along functors and comma-category infrastructure.
- `REPORT_EMDASH_V3_2_PROFUNCTOR_WEIGHTED_LIMITS_PRELIM_PLAN_2026-06-17.md`:
  active implementation plan and log for the v3.2 profunctor facade,
  tensor/internal-hom calculus, weighted limits, op-duality, and the
  join/directed-inductive stress test.
- `REPORT_EMDASH_V3_2_PROFUNCTOR_REPRESENTABILITY_REDESIGN_PRELIM_PLAN_2026-06-19.md`:
  proposed representability- and isomorphism-based redesign of the profunctor
  calculus, motivated by the current right-adjoint weighted-limit preservation
  architecture; also owns the trigger-based deferred-internalization side-task
  ledger.
- `REPORT_EMDASH_V3_2_GROUPOID_COMPUTATIONAL_UNIVALENCE_IMPLEMENTATION_PLAN_2026-06-23.md`:
  active architecture and staged implementation plan for observational
  groupoid paths, type equivalence, computational univalence,
  omega-categorical equivalence, explicit categorical-univalence capability,
  Yoneda internalization, and generic `HomComparison`.
- `REPORT_EMDASH_V3_2_DEFISO_HOM_ACTION_PROFCOMPARISON_MIGRATION_PLAN_2026-06-28.md`:
  proposed subplan for the `UNI-DEFISO` migration: stable hom-action owners,
  generic `hom_int` precomposition, Cat-specialized owner cleanup, and
  factoring `ProfComparison` through `DefIso`.
- `REPORT_EMDASH_V3_2_CAT_CATD_SPECIALIZATION_ALIAS_MIGRATION_PLAN_2026-07-04.md`:
  dedicated proposed subplan for demoting pure `Cat_cat`/`Catd_cat`
  specialized identity, composition, and curried-composition helpers to
  transparent aliases over generic `id`, `comp_fapp0`, and `hom_*` owners,
  while retaining Cat-only transfor projection heads.
- `REPORT_EMDASH_V3_2_PROF_CAT_PRIMITIVE_REDESIGN_PLAN_2026-07-06.md`:
  proposed plan for making `Prof_cat(A,B)` a primitive fixed-endpoint
  profunctor category head, with explicit `Obj`/`Hom_cat` projections to the
  existing `Catd_cat(Product_cat(Op_cat A) B)` semantics and public vertical
  normal forms over generic `@comp_fapp0 (Prof_cat A B)`.
- `REPORT_EMDASH_V3_2_COMP_PROD_FUNC_UNIT_PROF_ACTION_SUBPLAN_2026-07-07.md`:
  promoted subplan of the primitive-`Prof_cat` migration which adds the general
  product/uncurried composition owner `comp_prod_func`, deleting the residual
  `Unit_prof_fapp1_func` stable head, and cleaning historical hom-action
  equality wrappers.
- `REPORT_EMDASH_V3_2_HOM_VARIANCE_SEPARATION_AND_HOM_FAPP0_CLEANUP_PLAN_2026-07-09.md`:
  implemented and validated subplan separating covariant and contravariant hom
  owners at runtime, moving opposite/identity duality to narrow proof-time
  bridges, retargeting dependent consumers, and completing both object-level
  folds plus identity-endpoint degenerations for the general `Hom_fapp0`
  endpoint-action owner.
- `REPORT_EMDASH_V3_2_EQUIPMENT_SHADOW_TENSOR_JOIN_REDESIGN_PLAN_2026-06-28.md`:
  detailed redesign plan for retiring remaining `Prof_comp_transf`/
  equipment-shadow runtime ownership from tensor/co-Yoneda and primitive join,
  while retaining semantically justified `Prof_reindex`.
- `REPORT_EMDASH_V3_2_ECKMANN_HILTON_APPLICATION_PLAN_2026-07-03.md`:
  proposed reviewer-facing Eckmann-Hilton application plan, including
  proof-by-reflexivity boundaries, horizontal-composition normal-form probes,
  interchange theorem staging, and rewrite-rule SOP gates for any missing
  bridge.
- `REPORT_EMDASH_V3_2_FULL_NATURALITY_PRELIM_PLAN_2026-06-12.md`: full
  naturality follow-up plan.
- `REPORT_EMDASH_V3_2_FUNCTOR_STRUCTURAL_LOGIC_PRELIM_PLAN_2026-06-04.md`:
  structural functor logic and displayed follow-ups.
- `REPORT_EMDASH_V3_2_NOTATION_MIGRATION_AND_REORG_IMPLEMENTATION_PLAN_2026-06-05.md`:
  notation migration and checks-file split history.
- `REPORT_EMDASH_V3_2_INDEX_3_2_READABILITY_IMPLEMENTATION_PLAN_2026-06-06.md`:
  print/index readability plan.
- `REPORT_EMDASH_V3_2_RESEARCH_ARTICLE_ARCHITECTURE_2026-06-05.md`:
  research article architecture and paper narrative plan.

## Audits And Retirements

- `REPORT_EMDASH_V2_RETIREMENT_AUDIT_2026-06-16.md`: audit for retiring the
  obsolete v2 baseline and consolidated v2 report.

Retired source files and superseded reports live under ignored `.scratchpad/`
paths. Do not consult `.scratchpad/` during normal work unless explicitly
asked for historical recovery.

## Generated Or Semi-Generated Reports

The following reports are expected to be generated or refreshed by tooling:

- `REPORT_EMDASH_HEALTH.md`: validation and source metrics generated by
  `scripts/check_metrics.py`.
- `REPORT_EMDASH_CHECK_CATALOG.md`: reviewer-facing check catalog generated by
  `scripts/generate_check_catalog.py`.

## Maintenance Rules

- Add every new active report to this index.
- Give active plan reports stable `Plan-ID`, dependency, side-task-ledger, and
  Infinity Codex provenance fields. `make ci` enforces these fields for reports
  listed under Current Plans.
- Mark reports as current plans, audits, generated reports, or retired
  references.
- Keep active reports free of instructions to read `.scratchpad/`.
