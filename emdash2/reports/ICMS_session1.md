# ICMS 2026 Session 1 Abstract (Draft)

**Title:** emdash2: Rewrite-Driven Automation for Strict/Lax \(\omega\)-Categorical Reasoning in Lambdapi

We present **emdash2**, an ongoing Lambdapi development for functorial programming in strict/lax \(\omega\)-categories, with automation centered on definitional reduction rather than post-hoc rewriting by lemmas. The kernel exposes categories, functors, and transformations as first-class objects (`Cat`, `Functor_cat`, `Transf_cat`) and organizes higher cells via hom-categories and displayed/fibred constructions. A central engineering principle is to normalize through stable rewrite heads (`fapp0`, `fapp1_fapp0`, `tapp1_fapp0`, etc.) plus focused unification rules, so many coherence steps become computation during type checking.

Current milestones include computational interfaces for ordinary/displayed functor action, projection of transfor components, strict naturality rules for arrow-indexed components, and a draft exchange-law instance in representable Cat-valued settings. The file also introduces a phase-3 adjunction interface with explicit unit/counit transfors and an oriented triangle cut-elimination rule, connecting proof-theoretic normalization ideas to higher-categorical structure.

For mathematical software, the contribution is an executable algebraic specification style: symbolic categorical laws are encoded as typed rewrite systems that can be checked, iterated, and refined in a proof-assistant kernel. This provides a practical bridge toward AI-assisted formalization workflows, where LLM-generated candidates are validated by normalization and type checking.
