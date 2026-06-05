I agree with the direction. The report set should be cut down, but only after updating the remaining core files so no active guidance points at archived reports.

**Keep Active**
- `reports/REPORT_EMDASH2_CONSOLIDATED.md`
- `reports/EMDASH_FOUNDATIONS.md`
- `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`
- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`
- `reports/REPORT_EMDASH_V3_2_FUNCTOR_STRUCTURAL_LOGIC_PRELIM_PLAN_2026-06-04.md`
- `reports/REPORT_EMDASH_V3_2_NOTATION_MIGRATION_AND_REORG_IMPLEMENTATION_PLAN_2026-06-05.md`

I would not merge canonical syntax into `EMDASH_FOUNDATIONS.md` yet. Syntax is a presentation/parser authority; foundations is mathematical/architectural. Cross-link them, but keep separate.

**Archive After Consolidation**
Move these into something like `.scratchpad/retired/2026-06-05_reports_consolidation/`:

- `reports/REPORT_EMDASH_V3_FAITHFUL_SURFACE_SYNTAX_PLAN.md`
- `reports/REPORT_EMDASH_V3_CONSOLIDATED.md`
- `reports/REPORT_EMDASH_V3_2_SYNTHETIC_PATH_INDUCTION_CONSOLIDATED_PLAN_AND_STATUS_2026-05-31.md`
- `reports/REPORT_EMDASH_V3_2_PI_ALIAS_SIGMA_PROJ1_CONSOLIDATED_STATUS_2026-05-31.md`
- `reports/REPORT_EMDASH_V3_2_PAIR_TELE_CURRY_REARCHITECTURE_PLAN_2026-06-01.md`
- `reports/REPORT_EMDASH_V3_2_INTERNAL_ACTION_PROJECTION_PLAN_2026-06-03.md`
- `reports/REPORT_SIGMA_LAXITY_TRANSP_DISCUSSION_PRELIM_2026-06-03.md`

Before archiving, update:
- `REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`: make it the single current status/SOP source, aligned to the reorganized `emdash3_2.lp` section map.
- `EMDASH_FOUNDATIONS.md`: either update notation fully or keep it theory-focused with explicit pointer to canonical syntax.
- `README.md` and `AGENTS.md`: they currently reference reports that would be archived, especially the synthetic path-induction and internal-action reports.

The key consolidation rule: specialized reports should donate only their surviving facts into `CURRENT_STATUS_AND_SOP` or `EMDASH_FOUNDATIONS`; their exploration history belongs in `.scratchpad`.