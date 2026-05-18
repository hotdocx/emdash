Updated the SOP/comments as requested.

Changed:
- [emdash3_1.lp](/home/user1/emdash1/emdash2/emdash3_1.lp:48): explicitly warns that even stable compound expressions like `Op_cat (Hom_cat ...)` should not be spelled in implicit LHS slots.
- [emdash3_1.lp](/home/user1/emdash1/emdash2/emdash3_1.lp:876): fixed the `homd_` action comment to match the current `_ Cat_cat` LHS.
- [emdash3_1.lp](/home/user1/emdash1/emdash2/emdash3_1.lp:912): fixed the `piapp0` comment to say the base argument is intentionally implicit.
- [REPORT_EMDASH_V3_HOM_FAM_PI_CONST_PLAN.md](/home/user1/emdash1/emdash2/reports/REPORT_EMDASH_V3_HOM_FAM_PI_CONST_PLAN.md:75) and [REPORT_EMDASH_V3_CONSOLIDATED.md](/home/user1/emdash1/emdash2/reports/REPORT_EMDASH_V3_CONSOLIDATED.md:48): added the same rule to the reports.

Checks passed:
- `timeout 60s lambdapi check -w emdash3_1.lp`
- `EMDASH_TYPECHECK_TIMEOUT=60s make check`
- `git diff --check`

For `tdapp1_int_func_transfd` / `fdapp1_int_transfd`, yes, the feasible shape is clearer now:

1. Add a generalized internal hom head, something like:
   `homd_int_funcd [D E : Catd K] (FF : Functord D E) : Functord (Op_catd E) (Homd_target_catd D)`

2. Add displayed opposite:
   `Op_funcd FF : Functord (Op_catd E) (Op_catd D)` for `FF : Functord E D`.

3. Then the internal displayed action should have the v2 shape:
   `tdapp1_int_func_transfd FF GG : Functor (Transfd_cat FF GG) (Transfd_cat (homd_int_funcd id_E) (comp_catd_fapp0 (homd_int_funcd GG) (Op_funcd FF)))`

4. Identity specialization:
   `fapp0 (tdapp1_int_func_transfd FF FF) (id ...) ↪ fdapp1_int_transfd FF`

I would not add extra `tdapp1_int_fapp0_*` / hom-action packaging heads yet. The next implementation step should be just the generalized `homd_int_funcd`, `Op_funcd`, `tdapp1_int_func_transfd`, and `fdapp1_int_transfd` skeleton plus the identity fold.