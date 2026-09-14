require open emdash.emdash3_2_product_composition_paths;
require open emdash.emdash3_2_product_family_action_views;

/* Whole product-coordinate laws for native diagonal postcomposition. */

// Native diagonal precomposition preserves both original whole coordinates.
symbol diagonal_tuple_precompose_path [B C : Cat] (X0 X1 F G : τ (Functor B C)) (a : τ (@Transf B C X0 X1)) (f :
  τ (@Transf B C X1 F)) (g : τ (@Transf B C X1 G))
  : τ (@= (Hom (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G)) (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X1) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)
  (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F G)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Snd (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G)))) f g) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0 X1 a)) (@Struct_sigma (@Transf B C X0 F) (λ
  _ : τ (@Transf B C X0 F), @Transf B C X0 G) (@comp_fapp0 (Functor_cat B C) X0 X1 F f a) (@comp_fapp0 (Functor_cat B
  C) X0 X1 G g a)))
≔ @path_product_join (@Transf B C X0 F) (@Transf B C X0 G) (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X0) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X1) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat
  C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor
  B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Snd (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G)))) f g) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0 X1 a)) (@Struct_sigma (@Transf B C X0 F) (λ
  _ : τ (@Transf B C X0 F), @Transf B C X0 G) (@comp_fapp0 (Functor_cat B C) X0 X1 F f a) (@comp_fapp0 (Functor_cat B
  C) X0 X1 G g a)) (Struct_sigma (@eq_trans (@Transf B C X0 F) (sigma_Fst (@comp_fapp0 (Functor_cat B (Product_cat C
  C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X0) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X1) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat
  C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor
  B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Snd (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G)))) f g) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0 X1 a))) (@comp_fapp0 (Functor_cat B C) X0
  X1 F f (@sigma_Fst (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X0)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0)) (@sigma_Fst (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)))), (Obj (Hom_cat
  (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C))
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X0)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X1))))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0 X1 a))) (@comp_fapp0 (Functor_cat B C) X0
  X1 F f a) (@product_comp_first_path (Functor_cat B C) (Functor_cat B C) (@fapp0 (Functor_cat B C) (Functor_cat
  B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0) (@fapp0 (Functor_cat
  B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat
  B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0 X1 a) (@Struct_sigma
  (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Snd (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G)))) f g)) (@eq_ap (@Transf B C X0 X1) (@Transf B C X0 F) (λ k : τ (@Transf
  B C X0 X1), (@comp_fapp0 (Functor_cat B C) X0 X1 F f k)) (@sigma_Fst (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst
  (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)))) (λ
  _ : τ (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X0)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X1)))), (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ :
  τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _
  : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1))))) (@fapp1_fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0 X1 a)) a
  (@diagonal_family_native_proj1_path B C X0 X1 a))) (@eq_trans (@Transf B C X0 G) (sigma_Snd (@comp_fapp0
  (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) X0) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1))
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (λ _ : τ (Obj (Hom_cat
  (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Snd
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) f g) (@fapp1_fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0 X1 a)))
  (@comp_fapp0 (Functor_cat B C) X0 X1 G g (@sigma_Snd (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B
  C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0)) (@sigma_Fst (Obj (Functor_cat B C))
  (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B
  C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat
  B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)))),
  (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X0)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X1))))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0 X1 a))) (@comp_fapp0 (Functor_cat B C) X0
  X1 G g a) (@product_comp_second_path (Functor_cat B C) (Functor_cat B C) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X1) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X0 X1 a) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat
  B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1))
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (λ _ : τ (Obj (Hom_cat
  (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Snd
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) f g)) (@eq_ap (@Transf B C X0 X1) (@Transf
  B C X0 G) (λ k : τ (@Transf B C X0 X1), (@comp_fapp0 (Functor_cat B C) X0 X1 G g k)) (@sigma_Snd (Obj (Hom_cat
  (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C))
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X0)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C))
  (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _
  : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)))), (Obj (Hom_cat (Functor_cat B C)
  (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0))
  (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)))))
  (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X0 X1 a)) a (@diagonal_family_native_proj2_path B C X0 X1 a))));

// Native diagonal postcomposition preserves both original whole coordinates.
symbol diagonal_tuple_postcompose_path [B C : Cat] (F G Z0 Z1 : τ (Functor B C)) (f : τ (@Transf B C F Z0)) (g :
  τ (@Transf B C G Z0)) (a : τ (@Transf B C Z0 Z1))
  : τ (@= (Hom (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z1)) (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) Z0) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1) (@fapp1_fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0 Z1 a)
  (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))), Obj
  (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))
  (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)))) f g)) (@Struct_sigma (@Transf B C F Z1) (λ _ : τ (@Transf B C F Z1), @Transf B C
  G Z1) (@comp_fapp0 (Functor_cat B C) F Z0 Z1 a f) (@comp_fapp0 (Functor_cat B C) G Z0 Z1 a g)))
≔ @path_product_join (@Transf B C F Z1) (@Transf B C G Z1) (@comp_fapp0 (Functor_cat B (Product_cat C C))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1)
  (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0 Z1 a) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))) (λ _ : τ (Obj
  (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))
  (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G)) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))) f g)) (@Struct_sigma (@Transf B C F Z1)
  (λ _ : τ (@Transf B C F Z1), @Transf B C G Z1) (@comp_fapp0 (Functor_cat B C) F Z0 Z1 a f) (@comp_fapp0 (Functor_cat
  B C) G Z0 Z1 a g)) (Struct_sigma (@eq_trans (@Transf B C F Z1) (sigma_Fst (@comp_fapp0 (Functor_cat B (Product_cat C
  C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1)
  (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0 Z1 a) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))) (λ _ : τ (Obj
  (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))
  (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G)) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))) f g))) (@comp_fapp0 (Functor_cat B C) F
  Z0 Z1 (@sigma_Fst (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z0)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)) (@sigma_Fst (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1)))), (Obj (Hom_cat
  (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C))
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Z1))))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0 Z1 a)) f) (@comp_fapp0 (Functor_cat B C) F
  Z0 Z1 a f) (@product_comp_first_path (Functor_cat B C) (Functor_cat B C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z0) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1) (@Struct_sigma (Obj (Hom_cat (Functor_cat
  B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))), Obj (Hom_cat (Functor_cat B C)
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Snd (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))) f
  g) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0 Z1 a)) (@eq_ap (@Transf B C Z0 Z1) (@Transf B C F Z1) (λ k : τ (@Transf B C Z0 Z1),
  (@comp_fapp0 (Functor_cat B C) F Z0 Z1 k f)) (@sigma_Fst (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)) (@sigma_Fst (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1)))) (λ _ : τ (Obj
  (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B
  C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Z1)))), (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ :
  τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _
  : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1))))) (@fapp1_fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0 Z1 a)) a
  (@diagonal_family_native_proj1_path B C Z0 Z1 a))) (@eq_trans (@Transf B C G Z1) (sigma_Snd (@comp_fapp0
  (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z1) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0 Z1 a) (@Struct_sigma (Obj (Hom_cat
  (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))), Obj (Hom_cat (Functor_cat B C)
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Snd (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))) f
  g))) (@comp_fapp0 (Functor_cat B C) G Z0 Z1 (@sigma_Snd (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)) (@sigma_Fst (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1)))) (λ _ : τ (Obj
  (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B
  C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Z1)))), (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ :
  τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _
  : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1))))) (@fapp1_fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0 Z1 a)) g)
  (@comp_fapp0 (Functor_cat B C) G Z0 Z1 a g) (@product_comp_second_path (Functor_cat B C) (Functor_cat B C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1)
  (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))), Obj
  (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))
  (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)))) f g) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0 Z1 a)) (@eq_ap (@Transf B C Z0 Z1) (@Transf
  B C G Z1) (λ k : τ (@Transf B C Z0 Z1), (@comp_fapp0 (Functor_cat B C) G Z0 Z1 k g)) (@sigma_Snd (Obj (Hom_cat
  (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C))
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Z1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C))
  (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _
  : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1)))), (Obj (Hom_cat (Functor_cat B C)
  (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0))
  (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1)))))
  (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0 Z1 a)) a (@diagonal_family_native_proj2_path B C Z0 Z1 a))));

/* Native paired Hom composition, staged before identity specialization. */

// Compare the original complete tuple, with all four whole arrows retained.
symbol paired_tuple_source_diagonal_comp_path [B C : Cat] (X F0 G0 F1 G1 : τ (Functor B C)) (f : τ (@Transf B C
  X F0)) (g : τ (@Transf B C X G0)) (a : τ (@Transf B C F0 F1)) (b : τ (@Transf B C G0 G1))
  : τ (@= (Hom (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F1 G1)) (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F1 G1) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor
  B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F1 G1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1
  G1)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F0 G0)) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) a b) (@Struct_sigma
  (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F0 G0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat
  B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))), Obj (Hom_cat (Functor_cat B
  C) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0
  G0)))) f g)) (@Struct_sigma (@Transf B C X F1) (λ _ : τ (@Transf B C X F1), @Transf B C X G1) (@comp_fapp0
  (Functor_cat B C) X F0 F1 a f) (@comp_fapp0 (Functor_cat B C) X G0 G1 b g)))
≔ @path_product_join (@Transf B C X F1) (@Transf B C X G1) (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1) (@Struct_sigma (Obj (Hom_cat (Functor_cat B
  C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor
  B C) F1 G1)))) a b) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat
  B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0
  G0)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Snd (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F0 G0)))) f g)) (@Struct_sigma (@Transf B C X F1) (λ _ : τ (@Transf B C X F1),
  @Transf B C X G1) (@comp_fapp0 (Functor_cat B C) X F0 F1 a f) (@comp_fapp0 (Functor_cat B C) X G0 G1 b g))
  (Struct_sigma (@product_comp_first_path (Functor_cat B C) (Functor_cat B C) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F1 G1) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))) (λ _ : τ (Obj (Hom_cat
  (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F0 G0)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Snd
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))) f g) (@Struct_sigma (Obj (Hom_cat
  (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Snd (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)))) a b)) (@product_comp_second_path (Functor_cat B C) (Functor_cat B
  C) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1) (@Struct_sigma (Obj (Hom_cat (Functor_cat B
  C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0
  G0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))) f g) (@Struct_sigma (Obj
  (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0))
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) (λ _ : τ (Obj (Hom_cat
  (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))), Obj (Hom_cat (Functor_cat B C)
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Snd (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) a b)));

// Compare the original complete tuple, with all four whole arrows retained.
symbol paired_tuple_target_diagonal_comp_path [B C : Cat] (F0 G0 F1 G1 Z : τ (Functor B C)) (f : τ (@Transf B C
  F0 F1)) (g : τ (@Transf B C G0 G1)) (a : τ (@Transf B C F1 Z)) (b : τ (@Transf B C G1 Z))
  : τ (@= (Hom (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0
  G0) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)) (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) (λ _ : τ (Obj (Hom_cat (Functor_cat
  B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Fst (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F1 G1)) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) a b) (@Struct_sigma (Obj (Hom_cat
  (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Snd (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)))) f g)) (@Struct_sigma (@Transf B C F0 Z) (λ _ : τ (@Transf B C F0 Z),
  @Transf B C G0 Z) (@comp_fapp0 (Functor_cat B C) F0 F1 Z a f) (@comp_fapp0 (Functor_cat B C) G0 G1 Z b g)))
≔ @path_product_join (@Transf B C F0 Z) (@Transf B C G0 Z) (@comp_fapp0 (Functor_cat B (Product_cat C C))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F1 G1) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) Z) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) (λ _ :
  τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1
  G1)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C
  C) (@product_diagonal_func C)) Z)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) F1 G1)) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) a b) (@Struct_sigma (Obj (Hom_cat
  (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Snd (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)))) f g)) (@Struct_sigma (@Transf B C F0 Z) (λ _ : τ (@Transf B C F0 Z),
  @Transf B C G0 Z) (@comp_fapp0 (Functor_cat B C) F0 F1 Z a f) (@comp_fapp0 (Functor_cat B C) G0 G1 Z b g))
  (Struct_sigma (@product_comp_first_path (Functor_cat B C) (Functor_cat B C) (@Struct_sigma (Functor B C) (λ _
  : τ (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F1 G1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1
  G1)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F0 G0)) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) f g) (@Struct_sigma
  (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1))
  (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))), Obj (Hom_cat (Functor_cat B C)
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Snd (@fapp0 (Functor_cat
  B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) a
  b)) (@product_comp_second_path (Functor_cat B C) (Functor_cat B C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F1 G1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1
  G1)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F0 G0)) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) f g) (@Struct_sigma
  (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1))
  (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))), Obj (Hom_cat (Functor_cat B C)
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Snd (@fapp0 (Functor_cat
  B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) a
  b)));
