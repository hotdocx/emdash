require open emdash.emdash3_2_one_cat_adjunction_transpose_paths;
require open emdash.emdash3_2_product_family_tuple_paths;
require open emdash.emdash3_2_product_family_maps;
require open emdash.emdash3_2_one_cat_additive_family_paths;
require open emdash.emdash3_2_adjunction_untranspose_naturality;

/* Whole distribution through native mate naturality, with retained original inputs. */

// Only the inferred tuple presentation changes; f/g and the native mate are unchanged.
symbol one_cat_product_pair_native_input_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (X F G : τ (Functor B C))
  (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G))
  : τ (@= (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))
  (@one_cat_product_family_pair B C C1 Prod BP X F G f g) (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@Transf_cat
  B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (@one_cat_product_family_pair_func B C C1
  Prod BP X F G) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Snd (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G)))) f g)))
≔ (@eq_ap (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G))) (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G))) (λ u : τ (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat
  C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G))), (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@Transf_cat B C X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G))) (@one_cat_product_family_pair_func B C C1 Prod BP X F G) u)) (@Struct_sigma
  (@Transf B C X F) (λ _ : τ (@Transf B C X F), @Transf B C X G) f g) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))))
  (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) f g) (@eq_refl (Obj (Hom_cat
  (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G))) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Snd (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G)))) f g)));

// ⟨f,g⟩∘a = ⟨f∘a,g∘a⟩ as a path of whole transformations.
symbol one_cat_product_pair_precompose_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (X0 X1 F G : τ (Functor B C))
  (a : τ (@Transf B C X0 X1)) (f : τ (@Transf B C X1 F)) (g : τ (@Transf B C X1 G))
  : τ (@= (@Transf B C X0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (@comp_fapp0
  (Functor_cat B C) X0 X1 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))
  (@one_cat_product_family_pair B C C1 Prod BP X1 F G f g) a) (@one_cat_product_family_pair B C C1 Prod BP X0 F G
  (@comp_fapp0 (Functor_cat B C) X0 X1 F f a) (@comp_fapp0 (Functor_cat B C) X0 X1 G g a)))
≔ (@eq_trans (@Transf B C X0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (@comp_fapp0
  (Functor_cat B C) X0 X1 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))
  (@one_cat_product_family_pair B C C1 Prod BP X1 F G f g) a) (@comp_fapp0 (Functor_cat B C) X0 X1 (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X1) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@Transf_cat
  B C X1 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (@one_cat_product_family_pair_func B C C1
  Prod BP X1 F G) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Snd (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G)))) f g)) a) (@one_cat_product_family_pair B C C1 Prod BP X0 F G
  (@comp_fapp0 (Functor_cat B C) X0 X1 F f a) (@comp_fapp0 (Functor_cat B C) X0 X1 G g a)) (@eq_ap (@Transf B C X1
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (@Transf B C X0 (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G))) (λ h : τ (@Transf B C X1 (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G))), (@comp_fapp0 (Functor_cat B C) X0 X1 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F G)) h a)) (@one_cat_product_family_pair B C C1 Prod BP X1 F G f g) (@fapp0 (Hom_cat (Functor_cat B (Product_cat
  C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X1) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@Transf_cat
  B C X1 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (@one_cat_product_family_pair_func B C C1
  Prod BP X1 F G) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Snd (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G)))) f g)) (@one_cat_product_pair_native_input_path B C C1 Prod BP X1
  F G f g)) (@eq_trans (@Transf B C X0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (@comp_fapp0
  (Functor_cat B C) X0 X1 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@fapp0 (Hom_cat
  (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) X1) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F G)) (@Transf_cat B C X1 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))
  (@one_cat_product_family_pair_func B C C1 Prod BP X1 F G) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F G)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1))
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) f g)) a) (@fapp0 (Hom_cat
  (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) X0) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F G)) (@Transf_cat B C X0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))
  (@one_cat_product_family_pair_func B C C1 Prod BP X0 F G) (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@fapp0
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
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0 X1 a))) (@one_cat_product_family_pair B C
  C1 Prod BP X0 F G (@comp_fapp0 (Functor_cat B C) X0 X1 F f a) (@comp_fapp0 (Functor_cat B C) X0 X1 G g a))
  (@one_cat_transpose_precomp_path (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@one_cat_functor_category B C C1) (@one_cat_functor_category B (Product_cat C C) (@one_cat_product_category C C C1
  C1)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_cov_func B (Product_cat C C) C
  Prod) (@one_cat_postcomp_adjunction B C (Product_cat C C) C1 (@one_cat_product_category C C C1 C1)
  (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C C1 Prod BP)) X0 X1 (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F G) a (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1)) (sigma_Fst (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F G)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X1))
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) f g)) (@eq_ap (Obj (Hom_cat
  (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) X0) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F G))) (@Transf B C X0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (λ u : τ (Obj
  (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G))), (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@Transf_cat B C X0 (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G))) (@one_cat_product_family_pair_func B C C1 Prod BP X0 F G) u)) (@comp_fapp0
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
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X0 X1 a))
  (@Struct_sigma (@Transf B C X0 F) (λ _ : τ (@Transf B C X0 F), @Transf B C X0 G) (@comp_fapp0 (Functor_cat B C) X0
  X1 F f a) (@comp_fapp0 (Functor_cat B C) X0 X1 G g a)) (@diagonal_tuple_precompose_path B C X0 X1 F G a f
  g))));

// The native coproduct input retains the original two whole arrows.
symbol one_cat_copair_native_input_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (F G Z : τ (Functor B C))
  (f : τ (@Transf B C F Z)) (g : τ (@Transf B C G Z))
  : τ (@= (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) Z) (@one_cat_copair_family B C
  C1 Prod t A T0 F G Z f g) (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G)) Z) (@one_cat_copair_family_func B C C1 Prod t A T0 F G Z) (@Struct_sigma (Obj (Hom_cat
  (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))), Obj (Hom_cat (Functor_cat B C)
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Snd (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) f
  g)))
≔ (@eq_ap (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor
  B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z))) (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) Z) (λ u : τ (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C
  C) (@product_diagonal_func C)) Z))), (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)) (@Transf_cat B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G)) Z) (@one_cat_copair_family_func B C C1 Prod t A T0 F G Z) u)) (@Struct_sigma
  (@Transf B C F Z) (λ _ : τ (@Transf B C F Z), @Transf B C G Z) f g) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) (λ
  _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G)) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) f g) (@eq_refl (Obj (Hom_cat
  (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z))) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))),
  Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))
  (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)))) f g)));

// a∘[f,g] = [a∘f,a∘g] through the original whole inverse mate.
symbol one_cat_copair_postcompose_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (F G Z0 Z1 : τ (Functor B C))
  (f : τ (@Transf B C F Z0)) (g : τ (@Transf B C G Z0)) (a : τ (@Transf B C Z0 Z1))
  : τ (@= (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) Z1) (@comp_fapp0 (Functor_cat B
  C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) Z0 Z1 a (@one_cat_copair_family B C C1 Prod
  t A T0 F G Z0 f g)) (@one_cat_copair_family B C C1 Prod t A T0 F G Z1 (@comp_fapp0 (Functor_cat B C) F Z0 Z1 a f)
  (@comp_fapp0 (Functor_cat B C) G Z0 Z1 a g)))
≔ (@eq_trans (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) Z1) (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) Z0 Z1 a (@one_cat_copair_family B
  C C1 Prod t A T0 F G Z0 f g)) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F G)) Z0 Z1 a (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z0)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G)) Z0) (@one_cat_copair_family_func B C C1 Prod t A T0 F G Z0) (@Struct_sigma (Obj (Hom_cat
  (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))), Obj (Hom_cat (Functor_cat B C)
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Snd (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))) f
  g))) (@one_cat_copair_family B C C1 Prod t A T0 F G Z1 (@comp_fapp0 (Functor_cat B C) F Z0 Z1 a f) (@comp_fapp0
  (Functor_cat B C) G Z0 Z1 a g)) (@eq_ap (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) Z0) (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) Z1) (λ h : τ (@Transf B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) Z0), (@comp_fapp0 (Functor_cat B C) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) Z0 Z1 a h)) (@one_cat_copair_family B C C1 Prod t A T0 F G
  Z0 f g) (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C
  C) (@product_diagonal_func C)) Z0)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) Z0) (@one_cat_copair_family_func B C C1 Prod t A T0 F G Z0) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))) (λ
  _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G)) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))) f g))
  (@one_cat_copair_native_input_path B C C1 Prod t A T0 F G Z0 f g)) (@eq_trans (@Transf B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) Z1) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G)) Z0 Z1 a (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)) (@Transf_cat B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G)) Z0) (@one_cat_copair_family_func B C C1 Prod t A T0 F G Z0) (@Struct_sigma
  (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))
  (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))), Obj (Hom_cat (Functor_cat B C)
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Snd (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))) f
  g))) (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor
  B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z1)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) Z1) (@one_cat_copair_family_func B C C1 Prod t A T0 F G Z1) (@comp_fapp0 (Functor_cat B (Product_cat C C))
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
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))) f g))) (@one_cat_copair_family B C C1
  Prod t A T0 F G Z1 (@comp_fapp0 (Functor_cat B C) F Z0 Z1 a f) (@comp_fapp0 (Functor_cat B C) G Z0 Z1 a g))
  (@untranspose_postcomp_path (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@one_cat_postcomp_adjunction B
  (Product_cat C C) C (@one_cat_product_category C C C1 C1) C1 Prod (@product_diagonal_func C)
  (@one_cat_biproduct_adjunction C C1 Prod t A T0)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G) Z0 Z1 (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func
  B C (Product_cat C C) (@product_diagonal_func C)) Z0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (sigma_Fst (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z0)))), Obj
  (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))
  (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z0)))) f g) a) (@eq_ap (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1))) (@Transf B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G)) Z1) (λ u : τ (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1))), (@fapp0 (Hom_cat (Functor_cat B
  (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z1))
  (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) Z1) (@one_cat_copair_family_func B C
  C1 Prod t A T0 F G Z1) u)) (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z0) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
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
  G Z1) (@comp_fapp0 (Functor_cat B C) F Z0 Z1 a f) (@comp_fapp0 (Functor_cat B C) G Z0 Z1 a g))
  (@diagonal_tuple_postcompose_path B C F G Z0 Z1 f g a))));

// P(a,b)∘⟨f,g⟩=⟨a∘f,b∘g⟩ as a whole native mate law.
symbol one_cat_product_pair_target_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (X F0 G0 F1 G1 : τ (Functor B C))
  (f : τ (@Transf B C X F0)) (g : τ (@Transf B C X G0))
  (a : τ (@Transf B C F0 F1)) (b : τ (@Transf B C G0 G1))
  : τ (@= (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)) (@product_family_map B C Prod F0 G0 F1 G1 a b)
  (@one_cat_product_family_pair B C C1 Prod BP X F0 G0 f g)) (@one_cat_product_family_pair B C C1 Prod BP X F1 G1
  (@comp_fapp0 (Functor_cat B C) X F0 F1 a f) (@comp_fapp0 (Functor_cat B C) X G0 G1 b g)))
≔ (@eq_trans (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)) (@product_family_map B C Prod F0 G0 F1 G1 a b)
  (@one_cat_product_family_pair B C C1 Prod BP X F0 G0 f g)) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1
  G1)) (@product_family_map B C Prod F0 G0 F1 G1 a b) (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0))
  (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))
  (@one_cat_product_family_pair_func B C C1 Prod BP X F0 G0) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0
  G0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))) f g)))
  (@one_cat_product_family_pair B C C1 Prod BP X F1 G1 (@comp_fapp0 (Functor_cat B C) X F0 F1 a f) (@comp_fapp0
  (Functor_cat B C) X G0 G1 b g)) (@eq_ap (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0
  G0))) (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1))) (λ k : τ (@Transf B C X
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0))), (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F1 G1)) (@product_family_map B C Prod F0 G0 F1 G1 a b) k)) (@one_cat_product_family_pair B C C1 Prod BP X F0
  G0 f g) (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F0 G0)) (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0
  G0))) (@one_cat_product_family_pair_func B C C1 Prod BP X F0 G0) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0
  G0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))) f g))
  (@one_cat_product_pair_native_input_path B C C1 Prod BP X F0 G0 f g)) (@eq_trans (@Transf B C X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1))) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1
  G1)) (@product_family_map B C Prod F0 G0 F1 G1 a b) (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0))
  (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))
  (@one_cat_product_family_pair_func B C C1 Prod BP X F0 G0) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0
  G0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))) f g))) (@fapp0 (Hom_cat
  (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F1 G1)) (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))
  (@one_cat_product_family_pair_func B C C1 Prod BP X F1 G1) (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@fapp0
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
  _ : τ (Functor B C), Functor B C) F0 G0)))) f g))) (@one_cat_product_family_pair B C C1 Prod BP X F1 G1 (@comp_fapp0
  (Functor_cat B C) X F0 F1 a f) (@comp_fapp0 (Functor_cat B C) X G0 G1 b g)) (@one_cat_transpose_postcomp_path
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@one_cat_functor_category B C C1) (@one_cat_functor_category B
  (Product_cat C C) (@one_cat_product_category C C C1 C1)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@one_cat_postcomp_adjunction B C
  (Product_cat C C) C1 (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) Prod
  (@one_cat_binary_product_adjunction C C1 Prod BP)) X (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1) (@Struct_sigma (Obj (Hom_cat
  (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F0 G0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))), Obj (Hom_cat (Functor_cat B C)
  (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0
  G0)))) f g) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) (λ
  _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F0 G0)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))), Obj (Hom_cat
  (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Snd
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) a b)) (@eq_ap (Obj (Hom_cat (Functor_cat
  B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F1 G1))) (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1))) (λ u : τ (Obj
  (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F1 G1))), (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (@Transf_cat B C X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1))) (@one_cat_product_family_pair_func B C C1 Prod BP X F1 G1) u))
  (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)
  (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) (λ _ : τ
  (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0))
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))), Obj (Hom_cat (Functor_cat B
  C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Snd (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) a b) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0
  G0)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (sigma_Fst (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)))) f g)) (@Struct_sigma (@Transf
  B C X F1) (λ _ : τ (@Transf B C X F1), @Transf B C X G1) (@comp_fapp0 (Functor_cat B C) X F0 F1 a f) (@comp_fapp0
  (Functor_cat B C) X G0 G1 b g)) (@paired_tuple_source_diagonal_comp_path B C X F0 G0 F1 G1 f g a b))));

// [f,g]∘P(a,b)=[f∘a,g∘b] through the original coproduct mate.
symbol one_cat_copair_source_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (F0 G0 F1 G1 Z : τ (Functor B C))
  (a : τ (@Transf B C F0 F1)) (b : τ (@Transf B C G0 G1))
  (f : τ (@Transf B C F1 Z)) (g : τ (@Transf B C G1 Z))
  : τ (@= (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) Z) (@comp_fapp0 (Functor_cat
  B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F1 G1)) Z (@one_cat_copair_family B C C1 Prod t A T0 F1 G1 Z f g) (@product_family_map B C
  Prod F0 G0 F1 G1 a b)) (@one_cat_copair_family B C C1 Prod t A T0 F0 G0 Z (@comp_fapp0 (Functor_cat B C) F0 F1 Z f
  a) (@comp_fapp0 (Functor_cat B C) G0 G1 Z g b)))
≔ (@eq_trans (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) Z) (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)) Z (@one_cat_copair_family B C C1 Prod t A T0 F1 G1 Z f g)
  (@product_family_map B C Prod F0 G0 F1 G1 a b)) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1
  G1)) Z (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F1 G1) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Z)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1
  G1)) Z) (@one_cat_copair_family_func B C C1 Prod t A T0 F1 G1 Z) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat
  B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z))))
  (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) f g))
  (@product_family_map B C Prod F0 G0 F1 G1 a b)) (@one_cat_copair_family B C C1 Prod t A T0 F0 G0 Z
  (@comp_fapp0 (Functor_cat B C) F0 F1 Z f a) (@comp_fapp0 (Functor_cat B C) G0 G1 Z g b)) (@eq_ap (@Transf B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) Z) (@Transf B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F0 G0)) Z) (λ k : τ (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F1 G1)) Z), (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F0 G0)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) Z k (@product_family_map B C Prod F0
  G0 F1 G1 a b))) (@one_cat_copair_family B C C1 Prod t A T0 F1 G1 Z f g) (@fapp0 (Hom_cat (Functor_cat B (Product_cat
  C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z))
  (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) Z) (@one_cat_copair_family_func B
  C C1 Prod t A T0 F1 G1 Z) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat
  B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))),
  Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1))
  (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)))) f g)) (@one_cat_copair_native_input_path B C C1 Prod t A T0 F1 G1 Z f g))
  (@eq_trans (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) Z) (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)) Z (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)) (@Transf_cat B C (@fapp0 (Functor_cat
  B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F1 G1)) Z) (@one_cat_copair_family_func B C C1 Prod t A T0 F1 G1 Z)
  (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))), Obj
  (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1))
  (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)))) f g)) (@product_family_map B C Prod F0 G0 F1 G1 a b)) (@fapp0 (Hom_cat
  (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0
  G0)) Z) (@one_cat_copair_family_func B C C1 Prod t A T0 F0 G0 Z) (@comp_fapp0 (Functor_cat B (Product_cat C C))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F1 G1) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) Z) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) (λ _ :
  τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1
  G1)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C
  C) (@product_diagonal_func C)) Z)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) F1 G1)) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) f g) (@Struct_sigma (Obj (Hom_cat
  (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Snd (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)))) a b))) (@one_cat_copair_family B C C1 Prod t A T0 F0 G0 Z (@comp_fapp0
  (Functor_cat B C) F0 F1 Z f a) (@comp_fapp0 (Functor_cat B C) G0 G1 Z g b)) (@untranspose_precomp_path (Functor_cat
  B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) (@one_cat_postcomp_adjunction B (Product_cat C C) C
  (@one_cat_product_category C C C1 C1) C1 Prod (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t
  A T0)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) F1 G1) Z (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) F1 G1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F1 G1)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F0 G0)) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) a b)
  (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))), Obj
  (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1))
  (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)))) f g)) (@eq_ap (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z))) (@Transf B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F0 G0)) Z) (λ u : τ (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z))), (@fapp0 (Hom_cat (Functor_cat B
  (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z))
  (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) Z) (@one_cat_copair_family_func B
  C C1 Prod t A T0 F0 G0 Z) u)) (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Fst (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) (λ _ : τ (Obj (Hom_cat (Functor_cat
  B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (sigma_Fst (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F1 G1)) (sigma_Snd (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)))) f g) (@Struct_sigma (Obj (Hom_cat
  (Functor_cat B C) (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Snd (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)))) a b)) (@Struct_sigma (@Transf B C F0 Z) (λ _ : τ (@Transf B C F0 Z),
  @Transf B C G0 Z) (@comp_fapp0 (Functor_cat B C) F0 F1 Z f a) (@comp_fapp0 (Functor_cat B C) G0 G1 Z g b))
  (@paired_tuple_target_diagonal_comp_path B C F0 G0 F1 G1 Z a b f g))));
