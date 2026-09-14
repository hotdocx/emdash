/* Whole naturality after the existing postcomposition-family lift.
   Scope is the ordinary target; no caller component square is supplied. */
require open emdash.emdash3_2_one_cat_whiskering_paths;
require open emdash.emdash3_2_strict_transfor_component_paths;
require open emdash.emdash3_2_diagram_reindex_views;

symbol one_cat_family_naturality_path [B A C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) (F G : τ (Functor A C))
  (eta : τ (@Transf A C F G)) (D E : τ (Functor B A)) (alpha : τ (@Transf B A D E))
  : τ (@= (@Transf B C (@comp_cat_fapp0 B A C F D) (@comp_cat_fapp0 B A C G E))
      (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B A C F D) (@comp_cat_fapp0 B A C G D)
        (@comp_cat_fapp0 B A C G E)
        (@fapp1_fapp0 (Functor_cat B A) (Functor_cat B C) (@comp_cat_cov_func B A C G) D E alpha)
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B A C D F G) eta))
      (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B A C F D) (@comp_cat_fapp0 B A C F E)
        (@comp_cat_fapp0 B A C G E)
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B A C E F G) eta)
        (@fapp1_fapp0 (Functor_cat B A) (Functor_cat B C) (@comp_cat_cov_func B A C F) D E alpha)))
≔ @strict_component_naturality_path (Functor_cat B A) (Functor_cat B C)
    (@comp_cat_cov_func B A C F) (@comp_cat_cov_func B A C G)
    (@comp_cat_cov_func_func_transf B A C F G eta) D E alpha;

// Shape evaluation of the same whole whiskering, retaining native family endpoints.
symbol one_cat_diagram_family_whiskering_path [A B I C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (F G : τ (Functor A (Functor_cat I C))) (h : τ (@Transf A (Functor_cat I C) F G))
  (D : τ (Functor B A)) (i : τ (Obj I))
  : τ (@= (@Transf B C
      (@comp_cat_fapp0 B A C (@diagram_family_at_func A I C F i) D)
      (@comp_cat_fapp0 B A C (@diagram_family_at_func A I C G i) D))
      (@sym_transf_tapp0_transf B I C (@comp_cat_fapp0 B A (Functor_cat I C) F D)
        (@comp_cat_fapp0 B A (Functor_cat I C) G D)
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B A (Functor_cat I C) D F G) h) i)
      (@fapp0 _ _ (@comp_cat_con_fapp1_func B A C D
        (@diagram_family_at_func A I C F i) (@diagram_family_at_func A I C G i))
        (@sym_transf_tapp0_transf A I C F G h i)))
≔ @one_cat_whiskering_path A B (Functor_cat I C) C (@one_cat_functor_category I C C1) C1 D
    (@diagram_evaluation_at_func I C i) F G h;
