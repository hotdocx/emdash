require open emdash.emdash3_2;

/* Product-family action and its whole mate distribution laws. */

// The actual Hom action of original postcomposition, independent of product evidence.
symbol product_family_map_func [B C : Cat] [Prod : τ (Functor (Product_cat C C) C)] (F0 G0 F1 G1 : τ (Functor B
  C))
  : τ (Functor (Product_cat (@Transf_cat B C F0 F1) (@Transf_cat B C G0 G1)) (@Transf_cat B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1
  G1))))
≔ @fapp1_func (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F1 G1);

// Apply that native action to the original two whole arrows.
symbol product_family_map [B C : Cat] [Prod : τ (Functor (Product_cat C C) C)] (F0 G0 F1 G1 : τ (Functor B C))
  (a : τ (@Transf B C F0 F1)) (b : τ (@Transf B C G0 G1)) : τ (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))
≔ @fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (@Transf_cat B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F1 G1))) (@product_family_map_func B C Prod F0 G0 F1 G1) (@Struct_sigma (Obj (Hom_cat (Functor_cat B C)
  (sigma_Fst (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (sigma_Fst
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Fst (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)))), Obj (Hom_cat (Functor_cat B C) (sigma_Snd (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F0 G0)) (sigma_Snd (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor
  B C) F1 G1)))) a b);
