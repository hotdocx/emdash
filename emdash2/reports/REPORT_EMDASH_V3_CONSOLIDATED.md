# emdash v3 Consolidated Architecture

## Current Source of Truth

`emdash3_1.lp` is the active v3 iteration. The old tracked `emdash3.lp`
attempt is retired. Future v3 work should start from `emdash3_1.lp`, this
report, the detailed next-step plan
`reports/REPORT_EMDASH_V3_HOM_FAM_PI_CONST_PLAN.md`, and the repository SOP
in `AGENTS.md`.

The design goal is a Lambdapi specification for functorial programming over
omega-categories, using stable rewrite heads and unification helpers to make
normalization computational. The current checked v3.1 file still uses the
`Fam_*` directed-family vocabulary, but the agreed next architecture migrates
that vocabulary to canonical `Catd` names with the corrected semantics
`Catd_cat K ~= Functor_cat K Cat_cat`.

## Current v3.1 Baseline

- In the current file, directed families are ordinary functors into `Cat_cat`:
  `Fam_cat K := Functor_cat K Cat_cat`, with `Fam_app_cat E k` as the
  surface reading of `E[k]`.
- `Sigma_cat E` is the directed total category. Its object layer is
  `Sigma k : Obj K, Obj (E[k])`, and its hom-category is routed through the
  final dependent-hom endpoint `homd_`.
- `Functor_fam A B` internalizes the mixed-variance pointwise functor family:
  from `A : Fam (Op_cat K)` and `B : Fam K` it builds a family over `K` whose
  fibre is `Functor_cat (A[k]) (B[k])`.
- `Functor_mix_fam_func` packages this mixed-variance constructor as a functor
  so it is functorial in family arguments, not merely an object-level recipe.
- `Edge_fam Z : Functor (Op_cat Z) (Fam_cat Z)` is the internal edge family:
  at `x,y` it computes to `Op_cat (Hom_cat Z x y)`.
- `Presheaf_fam_func` and `HomPresheaf_fam` build the family
  `x |-> y |-> (Hom_Z(x,y)^op -> Cat)` using only internal functorial
  constructors.
- `Homd_source_fam`, `Homd_section_fam`, and `Homd_target_fam` name the
  source/target family expressions for the fully internal mixed-variance
  object `homd_int E : Homd E`.
- Endpoint projection is split into stable heads:
  `homd_src_func`, `homd_src_sec`, `homd_tgt_func`, then `homd_`.
- The final endpoint is definitionally the former sigma-hom formula:
  `homd_ E x u y v := hom_con v (fam_tapp0_func E x y u)`.

## Rewrite and Naming Discipline

- Do not reintroduce `homd_eval_func`, `Homd_func`, or `sigma_hom_fam` as
  current endpoint names. The current endpoint name is `homd_`.
- Avoid reducible compound expressions in inferred implicit positions of
  rewrite-rule LHSs. Use `_` for source/target family arguments when the
  actual inferred term contains `Functor_fam`, `HomPresheaf_fam`,
  `op_val_func`, or `comp_cat_fapp0`.
- Keep small stable-head projection steps instead of wrapping multiple
  projections in a single rewrite rule.
- Keep `Transf_cat` unification helpers. They are local elaboration aids that
  let rules such as `@tapp0_fapp0 ... _ _ ...` typecheck without forcing
  brittle family expressions into the LHS.
- Treat unification helpers for `Hom_cat`, `Functor_cat`, `Transf_cat`,
  `Fam`, and `Fam_app_cat` as controlled inference helpers, not broad semantic
  claims about every possible category constructor.

## Deferred Backlog

- Generic Sigma/Pi helper infrastructure remains deferred:
  `sigma_intro_transf`, `pi_eval_transf`, `const_section_func`, and
  `section_pullback_func`.
- The deferred shape is:

  ```text
  sigma_intro_transf E
    : Transf E (Const_fam K (Sigma_cat E))
  pi_eval_transf E
    : Transf (Const_fam K (Pi_cat E)) E
  const_section_func K A
    : A -> Pi_cat (Const_fam K A)
  section_pullback_func F E
    : Pi_cat E -> Pi_cat (Pullback_fam E F)
  ```

- These helpers should be reintroduced only after the directed-family core is
  stable enough to support robust beta assertions.
- When reintroduced, their rewrite rules should follow the same LHS hygiene:
  keep inferred family/category arguments implicit unless they are the actual
  discriminator.

The names above are the current v3.1 baseline names. During the next
architecture migration, translate them to the canonical `Catd` vocabulary
unless the detailed plan explicitly keeps a name as notation.

## Next Architecture Plan

The next implementation pass is governed by
`REPORT_EMDASH_V3_HOM_FAM_PI_CONST_PLAN.md`. Its main decisions are:

- Reuse the `Catd` suffix vocabulary, but with corrected directed-family
  semantics: `Catd_cat K` is the canonical contraction of
  `Functor_cat K Cat_cat`, not the older v2 isofibration reading.
- Keep aliases/definitions out of rewrite-rule LHSs. LHSs should use primitive
  stable heads and real discriminators.
- Make `Functor_cat` and `Transf_cat` rewrite-capable where needed, rather
  than keeping special contractions blocked by `constant`.
- Introduce stable contractions:

  ```text
  Functor_cat K Cat_cat --> Catd_cat K
  @Transf_cat K Cat_cat E D --> Functord_cat E D
  Hom_cat (Functord_cat E D) FF GG --> Transfd_cat FF GG
  ```

- Keep `Functord_cat` as the canonical category of natural/displayed functors
  between directed Cat-valued families, and `Transfd_cat` as the canonical
  category of displayed transfors/modifications.
- Keep `fdapp1_*` and `tdapp1_*` as genuine dependent stable heads. Fibrewise
  `fdapp1` notation can be derived, but the full dependent action over
  `homd_` cannot be replaced by ordinary fibrewise `fapp1_func`.
- Make `Pi_cat` a stable section category, with `piapp0` as derived
  section-evaluation notation and `piapp1_func` / `piapp1_fapp0` as stable
  terminal-specialization heads for full section action.
- Add terminal `homd_` normal forms needed by `piapp1_func`, especially:

  ```text
  homd_ (Terminal_catd K) x Terminal_obj y Terminal_obj
    --> Terminal_catd (Op_cat (Hom_cat K x y))
  ```

Future cleanup may rename or regroup symbols in `emdash3_1.lp`, but it should
follow the detailed phase order in the next-step plan.

## Retired v3 Material

The following tracked files were retired into
`.scratchpad/backup/2026-05-15_v3_retirement/` and should not be used as
current implementation guidance:

- `emdash3.lp`
- `PRD_EMDASH_V3_INITIAL_IDEA.md`
- `reports/emdash3_initial_implementation_plan.md`
- `reports/emdash3_internal_homd_reset_plan.md`
- `reports/emdash3_homd_rework_without_opaque_target_wrappers_plan.md`
- `reports/emdash3_catdd_predpi_implementation_plan.md`
- `reports/emdash3_foundations_internal_functoriality_sigma_hom_plan.md`
- `reports/emdash3_mix_variance_architecture.md`
- `reports/emdash3_1_mixed_variance_cleanup_plan.md`
- `reports/emdash3_1_homd_endpoint_stable_head_plan.md`
- `reports/REPORT_EMDASH_TYPESCRIPT_ELABORATION.md`
- `reports/REPORT_EMDASH_LOGIC_DEV_3.md`

The retired files are historical context only. Their old `Catd`, `Catdd`,
`PredPi_catd`, `homd_curry`, and `homd_eval_func` designs are superseded. The
new use of `Catd` terminology in the next-step plan is a corrected
directed-family contraction of `Functor _ Cat_cat`, not a return to the older
isofibration-style interpretation.

The repository cleanup implementation plan and other stale project notes were
also archived under `.scratchpad/backup/2026-05-15_project_docs_retirement/`
after consolidation. They are not current v3 guidance.

## Validation SOP

For v3.1 work, run:

```bash
lambdapi check -w emdash3_1.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

When changing rewrite rules, also add or update a focused assertion exercising
the stable head. If a check hangs, treat it as a likely rewrite or unification
problem and inspect the most recent LHS changes first.
