# EMDASH Reports Index

Date: 2026-07-11

Use this file as the first stop for report discovery. `emdash3_2.lp` remains
the active code authority; reports explain current status, mathematics,
notation, implementation plans, and historical decisions.

## Current Orientation

- `REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`:
  living current architecture, validation workflow, rewrite/unification SOP,
  and deferred boundaries.
- `EMDASH_FOUNDATIONS.md`: mathematician-facing guide to the implemented
  foundations and explicit staging limits.
- `REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`: notation
  authority for comments, examples, and future parser work.

## Current Plans

- `REPORT_EMDASH_V3_2_DISPLAYED_FACADE_TOWER_REARCHITECTURE_PLAN_2026-07-11.md`:
  proposed levelwise runtime/proof-time boundary between the displayed
  `Catd`/`Functord`/`Transfd` tower and the ordinary iterated-hom hierarchy,
  including Sigma omega-iteration and constant-section follow-up probes.
- `REPORT_EMDASH_MATHOPS_DEVOPS_IMPLEMENTATION_PLAN_2026-06-16.md`:
  active MathOps/DevOps/SOP improvement plan and utility roadmap.
- `REPORT_EMDASH_V3_2_PI_ALONG_FUNCTOR_IMPLEMENTATION_PLAN_2026-06-11.md`:
  proposed dependent products along functors and comma-category
  infrastructure.
- `REPORT_EMDASH_V3_2_PROFUNCTOR_REPRESENTABILITY_REDESIGN_PRELIM_PLAN_2026-06-19.md`:
  active representability/computational-comparison redesign and deferred
  internalization ledger.
- `REPORT_EMDASH_V3_2_GROUPOID_COMPUTATIONAL_UNIVALENCE_IMPLEMENTATION_PLAN_2026-06-23.md`:
  active groupoid, type-equivalence, computational-univalence,
  omega-equivalence, and generic comparison architecture.
- `REPORT_EMDASH_V3_2_DEFISO_HOM_ACTION_PROFCOMPARISON_MIGRATION_PLAN_2026-06-28.md`:
  active incremental `DefIso`, hom-action, and `ProfComparison` migration.
- `REPORT_EMDASH_V3_2_EQUIPMENT_SHADOW_TENSOR_JOIN_REDESIGN_PLAN_2026-06-28.md`:
  active/deferred redesign of remaining equipment-shadow, tensor,
  co-Yoneda, and primitive-join ownership.
- `REPORT_EMDASH_V3_2_FULL_NATURALITY_PRELIM_PLAN_2026-06-12.md`:
  full-naturality follow-up after the first implemented slice.
- `REPORT_EMDASH_V3_2_FUNCTOR_STRUCTURAL_LOGIC_PRELIM_PLAN_2026-06-04.md`:
  ordinary structural functor logic and displayed/product follow-ups.
- `REPORT_EMDASH_V3_2_PROFUNCTOR_WEIGHTED_LIMITS_PRELIM_PLAN_2026-06-17.md`:
  implementation log plus remaining profunctor, weighted-limit, duality, and
  directed-inductive follow-ups after the first end-to-end pass.

## Completed Or Promoted Decision Records

These reports remain active references for exact decisions and probe evidence,
but their promoted phases are not open implementation plans.

- `REPORT_EMDASH_V3_2_DOCUMENTATION_KERNEL_MAINTENANCE_IMPLEMENTATION_PLAN_2026-07-10.md`:
  completed authority consolidation, mathematical/notation refresh, adjacent
  documentation across executable sections 0–19, and diagnostic-navigation
  cleanup; broad naming and module-split work remains explicitly deferred.
- `REPORT_EMDASH_INFINITY_CODEX_IMPLEMENTATION_PLAN_2026-06-23.md`:
  completed local final-response archive and compaction/resume recovery flow.
- `REPORT_EMDASH_V3_2_NOTATION_MIGRATION_AND_REORG_IMPLEMENTATION_PLAN_2026-06-05.md`:
  completed notation/check-file split history with remaining work transferred
  to current maintenance/reorganization plans.
- `REPORT_EMDASH_V3_2_CAT_CATD_SPECIALIZATION_ALIAS_MIGRATION_PLAN_2026-07-04.md`:
  promoted generic-owner migration for Cat/Catd specialization aliases and
  retained Cat-only projection structure.
- `REPORT_EMDASH_V3_2_COMP_PROD_FUNC_UNIT_PROF_ACTION_SUBPLAN_2026-07-07.md`:
  promoted product-composition owner and direct unit-profunctor action.
- `REPORT_EMDASH_V3_2_HOM_VARIANCE_SEPARATION_AND_HOM_FAPP0_CLEANUP_PLAN_2026-07-09.md`:
  completed variance separation, rigid-`Hom` selection, proof-time comparison
  boundary, and middle-constrained identity follow-up.
- `REPORT_EMDASH_V3_2_PROF_CAT_PRIMITIVE_REDESIGN_PLAN_2026-07-06.md`:
  promoted primitive fixed-endpoint `Prof_cat`, public surface, and
  `Unit_prof`/representable reindex architecture.
- `REPORT_EMDASH_V3_2_ECKMANN_HILTON_APPLICATION_PLAN_2026-07-03.md`:
  promoted conservative Eckmann-Hilton computation and recorded broader
  textbook/presentation follow-ups.

## Deferred Reorganization And Presentation Plans

- `REPORT_EMDASH_V3_2_REORGANIZATION_PLAN_2026-06-16.md`: the first
  single-file section/assertion reorganization is reflected in the active
  source; module splitting remains deferred until boundaries stabilize.
- `REPORT_EMDASH_V3_2_INDEX_3_2_READABILITY_IMPLEMENTATION_PLAN_2026-06-06.md`:
  print/index readability work.
- `REPORT_EMDASH_V3_2_RESEARCH_ARTICLE_ARCHITECTURE_2026-06-05.md`:
  research-article and paper narrative architecture.

## Audits And Retirements

- `REPORT_EMDASH_V2_RETIREMENT_AUDIT_2026-06-16.md`: audit for retiring the
  obsolete v2 baseline and consolidated v2 report.

Retired source files and superseded reports live under ignored `.scratchpad/`
paths. Do not consult them during normal work unless historical recovery is
explicitly requested.

## Generated Or Semi-Generated Reports

- `REPORT_EMDASH_HEALTH.md`: generated validation, timing, source, and section
  metrics.
- `REPORT_EMDASH_CHECK_CATALOG.md`: generated reviewer-facing map of the
  diagnostic suite.

## Maintenance Rules

- Add every new active report to this index.
- List only genuinely open plans under `Current Plans`; move completed promoted
  plans to decision records without deleting their history.
- Current plans require `Plan-ID`, dependency, supersession, side-task-ledger,
  Infinity Codex provenance, and status fields. `make ci` enforces them.
- Mark reports as current orientation, current plan, completed decision record,
  deferred plan, audit, or generated report.
- Keep normal-work instructions pointed at active authorities rather than
  ignored historical material.
