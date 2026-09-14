/* Original components of arbitrary native inverse pairing. */
require open emdash.emdash3_2_one_cat_product_family_inverse_components;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C Prod)) (X F G : τ (Functor B C)) (h : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G)))) (b : τ (Obj B)) ⊢ @one_cat_product_family_unpair1_component_path B C C1 Prod BP X F G
  h b : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C F b)) (@tapp0_fapp0 B C X F b (sigma_Fst
  (@one_cat_product_family_unpair B C C1 Prod BP X F G h))) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C)
  C Prod (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) (@fapp0 B C F b) (@binary_products_proj1_fapp0 C Prod
  BP (@fapp0 B C F b) (@fapp0 B C G b)) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G)) b h)));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C Prod)) (X F G : τ (Functor B C)) (h : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G)))) (b : τ (Obj B)) (v : τ (Hom C (@fapp0 B C X b) (@fapp0 B C F b))) ⊢ @eq_refl (Hom C (@fapp0
  B C X b) (@fapp0 B C F b)) (@tapp0_fapp0 B C X F b (sigma_Fst (@one_cat_product_family_unpair B C C1 Prod BP X F G
  h))) : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C F b)) (@tapp0_fapp0 B C X F b (sigma_Fst
  (@one_cat_product_family_unpair B C C1 Prod BP X F G h))) v);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C Prod)) (X F G : τ (Functor B C)) (h : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G)))) (b : τ (Obj B)) ⊢ @one_cat_product_family_unpair2_component_path B C C1 Prod BP X F G
  h b : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C G b)) (@tapp0_fapp0 B C X G b (sigma_Snd
  (@one_cat_product_family_unpair B C C1 Prod BP X F G h))) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C)
  C Prod (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) (@fapp0 B C G b) (@binary_products_proj2_fapp0 C Prod
  BP (@fapp0 B C F b) (@fapp0 B C G b)) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G)) b h)));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C Prod)) (X F G : τ (Functor B C)) (h : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G)))) (b : τ (Obj B)) (v : τ (Hom C (@fapp0 B C X b) (@fapp0 B C G b))) ⊢ @eq_refl (Hom C (@fapp0
  B C X b) (@fapp0 B C G b)) (@tapp0_fapp0 B C X G b (sigma_Snd (@one_cat_product_family_unpair B C C1 Prod BP X F G
  h))) : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C G b)) (@tapp0_fapp0 B C X G b (sigma_Snd
  (@one_cat_product_family_unpair B C C1 Prod BP X F G h))) v);
