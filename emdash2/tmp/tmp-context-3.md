tmp-context-3.md

I reviewed the active v3.2 context, the current reports, and only the named obsolete sections of [cartierSolution13.lp](/home/user1/emdash1/emdash2/cartierSolution13.lp:1016). I made no edits. Baseline validation passes:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

**Main Judgment**
The old `cartierSolution13.lp` sections should not be ported directly. The old design is centered on a broad `mod A B` profunctor calculus with global substitution, tensor, implication, adjunction, and duality rewrite rules starting around [cartierSolution13.lp:562](/home/user1/emdash1/emdash2/cartierSolution13.lp:562). The v3.2 architecture deliberately decomposes those responsibilities into safer semantic owners: `hom_int`/`hom_con`, `Functor_catd`, `Hom_catd`, `Transf_catd`, `Sigma_cat`, `Pi_cat`, `homd_int`, `fdapp1_int_*`, and first-class `Adjunction`.

So I would implement the old ideas in dependency order, not in the obsolete file order.

**Recommended Order**
1. Start with `Pi_along_func` / comma infrastructure.
   This is the strongest next move. The current plan already identifies `Pi_along_func(f) : Catd(A) ⊢ Catd(B)` as the right-Kan/dependent-product owner, with fibres over outgoing comma categories. See [REPORT_EMDASH_V3_2_PI_ALONG_FUNCTOR_IMPLEMENTATION_PLAN_2026-06-11.md:70](/home/user1/emdash1/emdash2/reports/REPORT_EMDASH_V3_2_PI_ALONG_FUNCTOR_IMPLEMENTATION_PLAN_2026-06-11.md:70). This directly subsumes the old Kan-extension direction.

2. Then add `Pi_proj_func(K)` and only later split/total bridges.
   Do not rewrite projection Pi to strict fibrewise `Pi_cat(E[l])` globally. The report is right: that should be a comparison theorem or strict/cartesian specialization, not a kernel definitional rule.

3. Then implement displayed structural logic for `Functor_catd`.
   Ordinary weakening/exchange/contraction already landed in [emdash3_2.lp:5306](/home/user1/emdash1/emdash2/emdash3_2.lp:5306). The next displayed layer should follow the structural plan: `Functor_catd_const_funcd`, `Functor_catd_sym_funcd`, `Functor_catd_diag_funcd`, with `Transf_catd` behavior induced by hom-action, not an independent theory.

4. Only after that, revisit “modules/profunctors”.
   If we need a first-class profunctor facade, define it as a v3.2 surface over Cat-valued mixed-variance families, not as the old primitive `mod`. A plausible future shape is a Cat-valued family over `A^op × B`, but the graph/action details need probes because directed variance matters.

5. Tensor/co-Yoneda should come after comma/Pi and probably `Sigma_along_func`.
   The old tensor section starts at [cartierSolution13.lp:1695](/home/user1/emdash1/emdash2/cartierSolution13.lp:1695). In v3.2, tensor should likely be a left-Kan/Sigma-along construction with co-Yoneda as a specialized reduction, not a broad rewrite like `P ⊗ Unit -> P`.

6. Weighted limits should wait.
   The old limit proof at [cartierSolution13.lp:2247](/home/user1/emdash1/emdash2/cartierSolution13.lp:2247) depends on implication/tensor and adjunction transposition. v3.2 has ordinary `Adjunction` at [emdash3_2.lp:2757](/home/user1/emdash1/emdash2/emdash3_2.lp:2757), but not yet the old `Adj_cov_hom`/`Adj_con_hom` transpose interface. Add a narrow v3.2 transpose package only when the weighted-limit theorem needs it.

7. Duality should be owner-by-owner.
   The old duality section at [cartierSolution13.lp:2286](/home/user1/emdash1/emdash2/cartierSolution13.lp:2286) installs broad `Op_*` rewrites, including TODO-marked questionable ones. In v3.2, add duality bridges only for stable owners after probes: `Pi_along` vs `Sigma_along`, adjunction opposite, and limit/colimit packages.

The join-category section is a separate benchmark, not a prerequisite. The old version only sketches a recursor and limited naturality around [cartierSolution13.lp:1021](/home/user1/emdash1/emdash2/cartierSolution13.lp:1021). A correct v3.2 join would need a proper hom-family story, including cross-hom actions and probably an initial/empty hom direction. I would defer it until after the comma/Pi path is stable.

For the next implementation turn, I recommend starting with Phase 1 of the `Pi_f` plan: `CommaOut_cat`, `CommaOut_proj_func`, and `CommaOut_precomp_func`, in a temporary probe first, with focused assertions before touching `emdash3_2.lp`.