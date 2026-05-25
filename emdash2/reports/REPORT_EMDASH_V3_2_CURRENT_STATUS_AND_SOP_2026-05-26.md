# EMDASH v3.2 Current Status And SOP

Date: 2026-05-26

This report is the current orientation point for `emdash3_2.lp`. It consolidates
the useful implementation lessons from the older HOM/FAM/PI/CONST plan and
implementation log, plus the later Pi-alias, Sigma-projection, and internalized
path-induction work.

## Current Source Of Truth

- Active implementation: `emdash3_2.lp`.
- Current theory/design guide:
  `reports/REPORT_EMDASH_V3_INTERNALIZED_PATH_INDUCTION_PLAN.md`.
- Current implementation status:
  `reports/REPORT_EMDASH_V3_INTERNALIZED_PATH_INDUCTION_IMPLEMENTATION_REPORT_2026-05-26.md`.
- This report records repository-level SOP and retirement guidance.

Retired historical references:

- The old v3.1 baseline and superseded HOM/FAM/PI/CONST plan/report have been
  moved to ignored `.scratchpad/retired/2026-05-26_v3_1_hom_fam_pi_const/`.
- Do not consult those archived files during normal v3.2 work. Recover them
  only for explicitly requested historical comparison.

## Current v3.2 Status

`emdash3_2.lp` now has:

- directed Cat-valued families via `Catd_cat K` as the canonical normal form of
  `Functor_cat K Cat_cat`;
- `Pi_cat` as a section-category alias through `Functord_cat`;
- Sigma categories and `Sigma_proj1_pullback_catd` for projection pullbacks;
- internalized `Catd_cat_func`, `Pullback_catd_func`, and `Pi_int_funcd`
  infrastructure;
- fixed-`Z,x` path induction packages:
  `PathInd_src_catd`, `PathInd_tgt_catd`, and `PathInd_func`;
- outgoing-path family infrastructure:
  `PathOut_cat`, `PathOut_cat_func`, `PathOutMotives_catd`,
  `pathout_refl_obj`, and the provisional `pathout_refl_arrow_sec`;
- the fixed-`x` directed composition benchmark:
  `path_comp_sec(x)[p][z](q) == q o p`;
- `CompTarget_catd` as the semantic `hom_con` alias over `Catd_cat Z`, not as a
  primitive stable family head.

The current full check is:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

At the time of this report it checks:

```text
emdash2.lp
emdash3_2.lp
```

The old v3.1 baseline is no longer part of the ordinary check path.

## SOP: Rewrite And Conversion Hygiene

Probe before committing nontrivial rewrite changes:

```bash
cp emdash3_2.lp tmp_rule_probe.lp
timeout 30s lambdapi check -w tmp_rule_probe.lp
```

Add a focused assertion exercising the intended normal form. A rule that
typechecks but does not prove the assertion, or times out on it, is not ready.

Keep inferred source/target arguments implicit in rule LHSs unless they are the
real discriminator. The useful discriminator is usually the explicit data head:
for example `Op_funcd`, `comp_catd_fapp0`, `homd_int`, or `tapp0_fapp0`, not
the reducible endpoint categories around it.

When an explicit source/target category slot is needed in an assertion or rule,
prefer canonical normal forms:

```text
Hom_cat Z x y
Functord_cat Z (Rep_catd Z y) (Rep_catd Z x)
```

over reducible readability wrappers:

```text
Fibre_cat (CompTarget_catd Z x) y
```

The wrapper may compute in isolation, but nested explicit slots can make
conversion search brittle.

Prefer semantic definitions before adding new primitive stable heads. If a
semantic definition fails to compute, first check:

- whether a corresponding capped projection rule is missing, such as
  `fapp1_fapp0 (Op_func F)` when `fapp1_func (Op_func F)` already exists;
- whether explicit arguments force a reducible or non-canonical form;
- whether a helper alias duplicates a semantic body instead of routing through
  the named semantic constructor.

Do not duplicate semantic bodies in helper aliases. If a construction has a
named semantic constructor, readable helpers should call that constructor. The
`CompTarget_catd` cleanup is the model:

```text
CompTarget_catd Z x
  := hom_con (Catd_cat Z) (Rep_catd Z x) (Op_cat Z) (Rep_catd_func Z)

CompTarget_fapp1_func p
  := fapp1_fapp0 (CompTarget_catd Z x) p
```

No separate `CompTarget_fapp1_func_func` alias is needed; full hom-action is the
ordinary `fapp1_func (CompTarget_catd Z x)`.

## Stable Heads Policy

Stable heads are justified when later rules need a visible constructor or when a
focused probe shows that a semantic definition causes conversion blowups that
cannot be fixed by smaller projection rules or canonical endpoints.

Do not add a stable head merely because a readable alias appears in the surface
syntax. Readable aliases should normally be definitions.

Notation-only heads such as `Fibre_cat` should not receive broad injectivity or
unification helpers. `Fibre_cat E k` is notation for `fapp0 E k`; equality of
fibre categories should not generally recover the whole family and index.

## Completed Retirement

Completed on 2026-05-26:

1. This report and the current path-induction reports contain the actively
   useful SOP from the older HOM/FAM/PI/CONST plan and implementation log.
2. `scripts/check.sh`, `Makefile`, `README.md`, and `AGENTS.md` no longer put
   `emdash3_1.lp` in the ordinary check path.
3. The historical files were moved to
   `.scratchpad/retired/2026-05-26_v3_1_hom_fam_pi_const/`:

   ```text
   emdash3_1.lp
   reports/REPORT_EMDASH_V3_HOM_FAM_PI_CONST_PLAN.md
   reports/REPORT_EMDASH_V3_HOM_FAM_PI_CONST_IMPLEMENTATION_REPORT_2026-05-20.md
   ```

4. Validation after the move:

   ```bash
   EMDASH_TYPECHECK_TIMEOUT=60s make check
   ```
