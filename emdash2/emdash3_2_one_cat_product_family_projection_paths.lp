require open emdash.emdash3_2_one_cat_product_families;
require open emdash.emdash3_2_adjunction_untranspose_naturality;
require open emdash.emdash3_2_product_composition_paths;
require open emdash.emdash3_2_product_family_action_views;

/* Whole product projections and β through native inverse-mate naturality. */

// The same native inverse mate selects the original whole projection.
symbol one_cat_product_family_proj1 [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (F G : τ (Functor B C)) : τ (@Transf B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) F)
≔ sigma_Fst (@one_cat_product_family_unpair B C C1 Prod BP (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) F G (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))));

// The same native inverse mate selects the original whole projection.
symbol one_cat_product_family_proj2 [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (F G : τ (Functor B C)) : τ (@Transf B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) G)
≔ sigma_Snd (@one_cat_product_family_unpair B C C1 Prod BP (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) F G (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))));

// Unpair(h)'s coordinate is composition with that same whole projection.
symbol one_cat_product_family_unpair1_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (X F G : τ (Functor B C)) (h : τ (@Transf B C X
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))))
  : τ (@= (@Transf B C X F) (sigma_Fst (@one_cat_product_family_unpair B C C1 Prod BP X F G h)) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) F
  (@one_cat_product_family_proj1 B C C1 Prod BP F G) h))
≔ (@eq_trans (@Transf B C X F) (sigma_Fst (@one_cat_product_family_unpair B C C1 Prod BP X F G h)) (sigma_Fst
  (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G))) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)
  (@one_cat_product_family_unpair B C C1 Prod BP (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) F G (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) h))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) F
  (@one_cat_product_family_proj1 B C C1 Prod BP F G) h) (@eq_ap (Hom (Functor_cat B (Product_cat C C)) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@Transf B C
  X F) (λ k : τ (Hom (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G)), sigma_Fst k) (@one_cat_product_family_unpair B C C1 Prod BP X F G h) (@comp_fapp0
  (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G))) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)
  (@one_cat_product_family_unpair B C C1 Prod BP (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) F G (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) h)) (@eq_sym (Hom
  (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G)) (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G))) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)
  (@one_cat_product_family_unpair B C C1 Prod BP (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) F G (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) h))
  (@one_cat_product_family_unpair B C C1 Prod BP X F G h) (@untranspose_precomp_path (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@one_cat_postcomp_adjunction B C (Product_cat C C) C1 (@one_cat_product_category C C C1
  C1) (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C C1 Prod BP)) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) h
  (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))))) (@eq_trans
  (@Transf B C X F) (sigma_Fst (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G) (@one_cat_product_family_unpair B C C1 Prod BP (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G)) F G (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) h))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) F
  (@one_cat_product_family_proj1 B C C1 Prod BP F G) (@sigma_Fst (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst
  (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst
  (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))))), (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Snd (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G))))))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G)) h))) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F G)) F (@one_cat_product_family_proj1 B C C1 Prod BP F G) h) (@product_comp_first_path (Functor_cat
  B C) (Functor_cat B C) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G))) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) h)
  (@one_cat_product_family_unpair B C C1 Prod BP (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) F G (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))))) (@eq_ap
  (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C
  Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (@Transf B C X F) (λ k : τ (@Transf B
  C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))), (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) F (@one_cat_product_family_proj1 B C C1 Prod BP F G)
  k)) (@sigma_Fst (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))))), (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))))))) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) h)) h
  (@diagonal_family_native_proj1_path B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) h))));

// The projection of the whole native pairing recovers the original whole input.
symbol one_cat_product_family_pair_proj1_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (X F G : τ (Functor B C))
  (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G))
  : τ (@= (@Transf B C X F) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G)) F (@one_cat_product_family_proj1 B C C1 Prod BP F G) (@one_cat_product_family_pair B C C1 Prod BP X F G
  f g)) f)
≔ @eq_sym (@Transf B C X F) f (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F G)) F (@one_cat_product_family_proj1 B C C1 Prod BP F G) (@one_cat_product_family_pair B C C1 Prod BP X F
  G f g))
    (@one_cat_product_family_unpair1_path B C C1 Prod BP X F G (@one_cat_product_family_pair B C C1 Prod BP X F
  G f g));

// Unpair(h)'s coordinate is composition with that same whole projection.
symbol one_cat_product_family_unpair2_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (X F G : τ (Functor B C)) (h : τ (@Transf B C X
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))))
  : τ (@= (@Transf B C X G) (sigma_Snd (@one_cat_product_family_unpair B C C1 Prod BP X F G h)) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) G
  (@one_cat_product_family_proj2 B C C1 Prod BP F G) h))
≔ (@eq_trans (@Transf B C X G) (sigma_Snd (@one_cat_product_family_unpair B C C1 Prod BP X F G h)) (sigma_Snd
  (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G))) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)
  (@one_cat_product_family_unpair B C C1 Prod BP (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) F G (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) h))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) G
  (@one_cat_product_family_proj2 B C C1 Prod BP F G) h) (@eq_ap (Hom (Functor_cat B (Product_cat C C)) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@Transf B C
  X G) (λ k : τ (Hom (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G)), sigma_Snd k) (@one_cat_product_family_unpair B C C1 Prod BP X F G h) (@comp_fapp0
  (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G))) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)
  (@one_cat_product_family_unpair B C C1 Prod BP (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) F G (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) h)) (@eq_sym (Hom
  (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G)) (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G))) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)
  (@one_cat_product_family_unpair B C C1 Prod BP (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) F G (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) h))
  (@one_cat_product_family_unpair B C C1 Prod BP X F G h) (@untranspose_precomp_path (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@one_cat_postcomp_adjunction B C (Product_cat C C) C1 (@one_cat_product_category C C C1
  C1) (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C C1 Prod BP)) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) h
  (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))))) (@eq_trans
  (@Transf B C X G) (sigma_Snd (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G) (@one_cat_product_family_unpair B C C1 Prod BP (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G)) F G (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) h))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) G
  (@one_cat_product_family_proj2 B C C1 Prod BP F G) (@sigma_Snd (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst
  (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst
  (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))))), (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Snd (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G))))))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G)) h))) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F G)) G (@one_cat_product_family_proj2 B C C1 Prod BP F G) h) (@product_comp_second_path (Functor_cat
  B C) (Functor_cat B C) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G))) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) h)
  (@one_cat_product_family_unpair B C C1 Prod BP (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) F G (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))))) (@eq_ap
  (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C
  Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (@Transf B C X G) (λ k : τ (@Transf B
  C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))), (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) G (@one_cat_product_family_proj2 B C C1 Prod BP F G)
  k)) (@sigma_Snd (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))))), (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))))))) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) h)) h
  (@diagonal_family_native_proj2_path B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) h))));

// The projection of the whole native pairing recovers the original whole input.
symbol one_cat_product_family_pair_proj2_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (X F G : τ (Functor B C))
  (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G))
  : τ (@= (@Transf B C X G) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G)) G (@one_cat_product_family_proj2 B C C1 Prod BP F G) (@one_cat_product_family_pair B C C1 Prod BP X F G
  f g)) g)
≔ @eq_sym (@Transf B C X G) g (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F G)) G (@one_cat_product_family_proj2 B C C1 Prod BP F G) (@one_cat_product_family_pair B C C1 Prod BP X F
  G f g))
    (@one_cat_product_family_unpair2_path B C C1 Prod BP X F G (@one_cat_product_family_pair B C C1 Prod BP X F
  G f g));
