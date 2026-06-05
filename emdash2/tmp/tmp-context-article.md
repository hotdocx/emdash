I reviewed the print SOP, the v2 long/short articles, the v3.2 source/checks, the foundations report, and the canonical syntax report. I wrote the consolidated article design here:

[REPORT_EMDASH_V3_2_RESEARCH_ARTICLE_ARCHITECTURE_2026-06-05.md](/home/user1/emdash1/emdash2/reports/REPORT_EMDASH_V3_2_RESEARCH_ARTICLE_ARCHITECTURE_2026-06-05.md)

Core recommendation: the v3.2 article should not patch the v2 paper in place. It should lead with the new computation:

```text
PathOut_Z(x) = Σ y :^n Z, Hom_Z(x,y)
rho_{x,y,p} : (x,id_x) -> (y,p)
PathInd_transfd(Z)
path_comp_sec(x)[p][z](q) = q o p
```

The narrative should present `PathInd_transfd` as the primary theorem, with `PathInd_funcd` as the derived Sigma-total presentation. The old v2 material is useful only as rhetorical scaffolding: stable heads, normalization-as-diagram-chasing, and some diagram styles. Its old `Catd`/Grothendieck/dependent-hom exposition should be demoted or replaced.

Recommended next step: create `print/public/index_3_2.md` as a long-form workbench article, preview with `/?paper=index_3_2.md`, then promote it to `index.md` once it renders cleanly. The short `index_0.md` should be regenerated after the long version stabilizes.

Validation done for this step: `git diff --check` on the new report.