/* Stage component computation at generic functors before specialization. */
require open emdash.emdash3_2_one_cat_whiskering_paths;

// Observe generic prewhiskering before specializing the whole transfor.
symbol prewhisker_component_path [B A C : Cat]
  (D : τ (Functor B A)) (F G : τ (Functor A C)) (eta : τ (@Transf A C F G)) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 A C F (@fapp0 B A D b)) (@fapp0 A C G (@fapp0 B A D b)))
      (@tapp0_fapp0 B C (@comp_cat_fapp0 B A C F D) (@comp_cat_fapp0 B A C G D) b
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B A C D F G) eta))
      (@tapp0_fapp0 A C F G (@fapp0 B A D b) eta))
≔ @eq_refl (Hom C (@fapp0 A C F (@fapp0 B A D b)) (@fapp0 A C G (@fapp0 B A D b)))
    (@tapp0_fapp0 A C F G (@fapp0 B A D b) eta);

// Observe postwhiskering with the original native source-family parent retained.
symbol postwhisker_native_source_component_path [B A C : Cat]
  (V : τ (Functor A C)) (F G : τ (Functor B A)) (eta : τ (@Transf B A F G)) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 A C V (@fapp0 B A F b)) (@fapp0 A C V (@fapp0 B A G b)))
      (@tapp0_fapp0 B C (@fapp0 (Functor_cat B A) (Functor_cat B C) (@comp_cat_cov_func B A C V) F) (@comp_cat_fapp0 B A C V G) b
        (@fapp0 _ _ (@comp_cat_cov_fapp1_func B A C V F G) eta))
      (@fapp1_fapp0 A C V (@fapp0 B A F b) (@fapp0 B A G b) (@tapp0_fapp0 B A F G b eta)))
≔ @eq_refl (Hom C (@fapp0 A C V (@fapp0 B A F b)) (@fapp0 A C V (@fapp0 B A G b)))
    (@fapp1_fapp0 A C V (@fapp0 B A F b) (@fapp0 B A G b) (@tapp0_fapp0 B A F G b eta));
