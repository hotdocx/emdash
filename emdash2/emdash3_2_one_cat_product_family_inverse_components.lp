/* Read native inverse pairing through its actual forward mate and cut. */
require open emdash.emdash3_2_one_cat_product_families;

// Sigma elimination exposes only the argument of the whole pairing functor.
symbol one_cat_product_family_pair_tuple_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (X F G : τ (Functor B C))
  (u : τ (Obj (Product_cat (@Transf_cat B C X F) (@Transf_cat B C X G)))) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G
  b)))) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) b (@fapp0 (Hom_cat
  (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B
  C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G)) (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))
  (@one_cat_product_family_pair_func B C C1 Prod BP X F G) u)) (@binary_products_pair_fapp0 C Prod BP (@fapp0 B C X b)
  (@fapp0 B C F b) (@fapp0 B C G b) (@tapp0_fapp0 B C X F b (sigma_Fst u)) (@tapp0_fapp0 B C X G b (sigma_Snd u))))
≔ @sigma_ind (@Transf B C X F) (λ _ : τ (@Transf B C X F), (@Transf B C X G))
    (λ u : τ (Obj (Product_cat (@Transf_cat B C X F) (@Transf_cat B C X G))), @= (Hom C (@fapp0 B C X b) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b)))) (@tapp0_fapp0 B C X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) b (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C))
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@Transf_cat
  B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (@one_cat_product_family_pair_func B C C1
  Prod BP X F G) u)) (@binary_products_pair_fapp0 C Prod BP (@fapp0 B C X b) (@fapp0 B C F b) (@fapp0 B C G b)
  (@tapp0_fapp0 B C X F b (sigma_Fst u)) (@tapp0_fapp0 B C X G b (sigma_Snd u))))
    (λ f : τ (@Transf B C X F), λ g : τ (@Transf B C X G), @one_cat_product_family_pair_component_path B C C1 Prod BP
  X F G f g b) u;

// Original projection observes the component selected by the native inverse mate.
symbol one_cat_product_family_unpair1_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
  τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (X F G : τ (Functor B C))
  (h : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C F b)) (@tapp0_fapp0 B C X F b (sigma_Fst (@one_cat_product_family_unpair
  B C C1 Prod BP X F G h))) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
  (@fapp0 B C F b) (@fapp0 B C G b))) (@fapp0 B C F b) (@binary_products_proj1_fapp0 C Prod BP (@fapp0 B C F b)
  (@fapp0 B C G b)) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) b h)))
≔ @eq_sym (Hom C (@fapp0 B C X b) (@fapp0 B C F b)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) (@fapp0 B C F b) (@binary_products_proj1_fapp0 C Prod BP
  (@fapp0 B C F b) (@fapp0 B C G b)) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) b h)) (@tapp0_fapp0 B C X F b (sigma_Fst (@one_cat_product_family_unpair B C C1 Prod BP X F G h)))
    (@eq_ap (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G
  b)))) (Hom C (@fapp0 B C X b) (@fapp0 B C F b)) (λ k : τ (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b)))), @comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C
  Prod (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) (@fapp0 B C F b) (@binary_products_proj1_fapp0 C Prod BP
  (@fapp0 B C F b) (@fapp0 B C G b)) k)
      (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) b h)
  (@binary_products_pair_fapp0 C Prod BP (@fapp0 B C X b) (@fapp0 B C F b) (@fapp0 B C G b) (@tapp0_fapp0 B C X F b
  (sigma_Fst (@one_cat_product_family_unpair B C C1 Prod BP X F G h))) (@tapp0_fapp0 B C X G b (sigma_Snd
  (@one_cat_product_family_unpair B C C1 Prod BP X F G h)))) (@one_cat_product_family_pair_tuple_component_path
  B C C1 Prod BP X F G (@one_cat_product_family_unpair B C C1 Prod BP X F G h) b));

// Original projection observes the component selected by the native inverse mate.
symbol one_cat_product_family_unpair2_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
  τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (X F G : τ (Functor B C))
  (h : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C G b)) (@tapp0_fapp0 B C X G b (sigma_Snd (@one_cat_product_family_unpair
  B C C1 Prod BP X F G h))) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
  (@fapp0 B C F b) (@fapp0 B C G b))) (@fapp0 B C G b) (@binary_products_proj2_fapp0 C Prod BP (@fapp0 B C F b)
  (@fapp0 B C G b)) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) b h)))
≔ @eq_sym (Hom C (@fapp0 B C X b) (@fapp0 B C G b)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) (@fapp0 B C G b) (@binary_products_proj2_fapp0 C Prod BP
  (@fapp0 B C F b) (@fapp0 B C G b)) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) b h)) (@tapp0_fapp0 B C X G b (sigma_Snd (@one_cat_product_family_unpair B C C1 Prod BP X F G h)))
    (@eq_ap (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G
  b)))) (Hom C (@fapp0 B C X b) (@fapp0 B C G b)) (λ k : τ (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b)))), @comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C
  Prod (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) (@fapp0 B C G b) (@binary_products_proj2_fapp0 C Prod BP
  (@fapp0 B C F b) (@fapp0 B C G b)) k)
      (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) b h)
  (@binary_products_pair_fapp0 C Prod BP (@fapp0 B C X b) (@fapp0 B C F b) (@fapp0 B C G b) (@tapp0_fapp0 B C X F b
  (sigma_Fst (@one_cat_product_family_unpair B C C1 Prod BP X F G h))) (@tapp0_fapp0 B C X G b (sigma_Snd
  (@one_cat_product_family_unpair B C C1 Prod BP X F G h)))) (@one_cat_product_family_pair_tuple_component_path
  B C C1 Prod BP X F G (@one_cat_product_family_unpair B C C1 Prod BP X F G h) b));
