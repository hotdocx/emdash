**Findings**

1. [index_3_2.md:262](/home/user1/emdash1/emdash2/print/public/index_3_2.md:262) slightly overstates the Sigma-hom equation. The source kernel normal form is
   `Op_cat (Sigma_cat (Op_cat (Hom_cat ...)) homd_)`, not literally the displayed Sigma formula as a whole hom-category equality; see [emdash3_2.lp:2627](/home/user1/emdash1/emdash2/emdash3_2.lp:2627) and [emdash3_2_checks.lp:3677](/home/user1/emdash1/emdash2/emdash3_2_checks.lp:3677). The article’s formula is fine as a 1-cell/object-level reading, but it should say that explicitly to avoid hiding 2-cell orientation.

2. [index_3_2.md:511](/home/user1/emdash1/emdash2/print/public/index_3_2.md:511) does not explicitly state the contravariant orientation of `PathOut_Z(p)`. The source says `PathOut_transport_func(p) : PathOut_Z(y) ⊢ PathOut_Z(x)` for `p : x → y`; see [emdash3_2.lp:3113](/home/user1/emdash1/emdash2/emdash3_2.lp:3113). Add that before `p_*E = PathOut_Z(p)^*E`, because this is a common place for readers to get turned around.

3. [index_3_2.md:566](/home/user1/emdash1/emdash2/print/public/index_3_2.md:566) says `PathInd_funcd(Z) = Σ(PathInd_transfd(Z))`. That is readable but under-specified: the implementation is specifically `Sigma_transfd_funcd ... PathInd_transfd`; see [emdash3_2.lp:3450](/home/user1/emdash1/emdash2/emdash3_2.lp:3450). I would write the formula as “`PathInd_funcd(Z) = Sigma_transfd_funcd(PathInd_transfd(Z))`”, with `Σ(...)` only as a prose abbreviation.

4. [index_3_2.md:147](/home/user1/emdash1/emdash2/print/public/index_3_2.md:147) promises Appendix A collects identifier correspondences, but [Appendix A](/home/user1/emdash1/emdash2/print/public/index_3_2.md:973) omits several identifiers used in the main text, including `Sigma_cat`, `Pi_cat`, `sigma_arrow`, `sigma_transport_arrow`, `homd_`, `piapp0`, `fib_cov_tapp0_func`, `Pullback_catd`, and `Sigma_transfd_funcd`. Either expand Appendix A or weaken the promise.

5. [index_3_2.md:684](/home/user1/emdash1/emdash2/print/public/index_3_2.md:684) uses `q` and `id_y` in the representable strictness equation without locally declaring `q : y → z`. The rule is correct against [emdash3_2.lp:4855](/home/user1/emdash1/emdash2/emdash3_2.lp:4855), but the paper should introduce `z` and `q` before the displayed formula.

6. [index_3_2.md:100](/home/user1/emdash1/emdash2/print/public/index_3_2.md:100) says “four checked contributions” and then lists five. Pure coherence/editing issue.

**Assessment**

The main theorem narrative is coherent and mostly correct against `emdash3_2.lp`, `emdash3_2_checks.lp`, and the reports. The strongest parts are the foundation-first flow, the primary-vs-derived theorem distinction, the non-circular `fdapp1_int_hom_fapp0`/`fdapp1_int_cell` laxity story, and the composition benchmark. The remaining issues are precision and reader-contract issues rather than fundamental mathematical errors.

Validation run during review:
`npm run validate:paper`, `EMDASH_TYPECHECK_TIMEOUT=60s make check`, and `npm run check:render` all passed. The render check still emits the existing Vite chunk-size warning.