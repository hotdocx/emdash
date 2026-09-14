/* Whole shearing is built before its scalar inverse evidence is supplied. */
require open emdash.emdash3_2_one_cat_additive_family_paths;
require open emdash.emdash3_2_additive_shears;
require open emdash.emdash3_2_one_cat_product_family_inverse_components;
require open emdash.emdash3_2_strict_pointwise_equivalences;

// Native inverse pairing of id supplies the original whole projection.
symbol one_cat_double_family_proj1 [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (X : τ (Functor B C)) : τ (@Transf B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X)
≔ sigma_Fst (@one_cat_product_family_unpair B C C1 Prod (@additive_binary_products C Prod t A) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) X X (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X))));

// Its component retains the original product projection.
symbol one_cat_double_family_proj1_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (X : τ (Functor B C)) (b : τ
  (Obj B))
  : τ (@= (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X
  b)) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X b
  (@one_cat_double_family_proj1 B C C1 Prod t A X)) (@binary_products_proj1_fapp0 C Prod
  (@additive_binary_products C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b)))
≔ @one_cat_product_family_unpair1_component_path B C C1 Prod (@additive_binary_products C Prod t A) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X X (@id (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X))) b;

// Native inverse pairing of id supplies the original whole projection.
symbol one_cat_double_family_proj2 [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (X : τ (Functor B C)) : τ (@Transf B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X)
≔ sigma_Snd (@one_cat_product_family_unpair B C C1 Prod (@additive_binary_products C Prod t A) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) X X (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X))));

// Its component retains the original product projection.
symbol one_cat_double_family_proj2_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (X : τ (Functor B C)) (b : τ
  (Obj B))
  : τ (@= (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X
  b)) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X b
  (@one_cat_double_family_proj2 B C C1 Prod t A X)) (@binary_products_proj2_fapp0 C Prod
  (@additive_binary_products C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b)))
≔ @one_cat_product_family_unpair2_component_path B C C1 Prod (@additive_binary_products C Prod t A) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X X (@id (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X))) b;

// S=(π₁,π₁+π₂) is an actual whole transformation on the original double product.
symbol one_cat_shear_family [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat
  C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ
  (Functor B C)) : τ (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)))
≔ @one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) (@fapp0 (Functor_cat B (Product_cat
  C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X X)) X X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod t A
  X));

// Scalar agreement is derived from the whole program's existing component observations.
symbol one_cat_shear_family_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X : τ (Functor B C)) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_shear_family B C C1 Prod t A T0 X)) (@additive_shear C Prod t A (@fapp0 B C X b)))
≔ (@eq_trans (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_shear_family B C C1 Prod t A T0 X)) (@binary_products_pair_fapp0 C Prod
  (@additive_binary_products C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0
  B C X b))) (@fapp0 B C X b) (@fapp0 B C X b) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X b (@one_cat_double_family_proj1 B C C1 Prod t A X)) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X b (@one_cat_additive_family_add B C C1 Prod t A T0
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1
  Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod t A X)))) (@additive_shear C Prod t A (@fapp0 B C
  X b)) (@one_cat_product_family_pair_component_path B C C1 Prod (@additive_binary_products C Prod t A) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod t A X))
  b) (@additive_pair_congr_path C Prod t A (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b)
  (@fapp0 B C X b))) (@fapp0 B C X b) (@fapp0 B C X b) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X b (@one_cat_double_family_proj1 B C C1 Prod t A X)) (@binary_products_proj1_fapp0 C
  Prod (@additive_binary_products C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b)) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X b (@one_cat_additive_family_add B C C1 Prod t A T0
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1
  Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod t A X))) (@preadditive_hom_add C (@additive_preadditive
  C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b)
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b))
  (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b)))
  (@one_cat_double_family_proj1_component_path B C C1 Prod t A X b) (@eq_trans (Hom C (@fapp0 (Product_cat C C)
  C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b)) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X b (@one_cat_additive_family_add B C C1 Prod t A T0
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1
  Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod t A X))) (@preadditive_hom_add C (@additive_preadditive
  C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b)
  (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X b
  (@one_cat_double_family_proj1 B C C1 Prod t A X)) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X b (@one_cat_double_family_proj2 B C C1 Prod t A X))) (@preadditive_hom_add C
  (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C
  X b))) (@fapp0 B C X b) (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) (@fapp0 B C X b)
  (@fapp0 B C X b)) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) (@fapp0 B C X b)
  (@fapp0 B C X b))) (@one_cat_additive_family_add_component_path B C C1 Prod t A T0 (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_double_family_proj2 B C C1 Prod t A X) b) (@additive_add_congr_path C Prod t A (@fapp0 (Product_cat
  C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X b (@one_cat_double_family_proj1 B C C1 Prod t A X))
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b))
  (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X b
  (@one_cat_double_family_proj2 B C C1 Prod t A X)) (@binary_products_proj2_fapp0 C Prod
  (@additive_binary_products C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b))
  (@one_cat_double_family_proj1_component_path B C C1 Prod t A X b)
  (@one_cat_double_family_proj2_component_path B C C1 Prod t A X b)))));

// Component equivalence retains the original scalar inverse while fixing actual S_b.
symbol one_cat_shear_family_component_omega [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X : τ (Functor B C)) (b : τ (Obj B))
  : τ (@OmegaEquivAlong C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_shear_family B C C1 Prod t A T0 X)))
≔ @omega_equiv_along_intro C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_shear_family B C C1 Prod t A T0 X)) (@additive_shear_inverse C Prod t A (@fapp0 B C X
  b)) (@additive_shear_inverse C Prod t A (@fapp0 B C X b)) (@eq_trans (Hom C (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B
  C X b) (@fapp0 B C X b)))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b)
  (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@additive_shear_inverse C
  Prod t A (@fapp0 B C X b)) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_shear_family B C C1 Prod t
  A T0 X))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C
  Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@additive_shear_inverse C Prod t A (@fapp0 B C X
  b)) (@additive_shear C Prod t A (@fapp0 B C X b))) (@id C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
  (@fapp0 B C X b) (@fapp0 B C X b)))) (@eq_ap (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C
  X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))))
  (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat
  C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))) (λ h : τ (Hom C (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B
  C X b) (@fapp0 B C X b)))), (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b)
  (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@additive_shear_inverse C
  Prod t A (@fapp0 B C X b)) h)) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_shear_family B C C1 Prod t
  A T0 X)) (@additive_shear C Prod t A (@fapp0 B C X b)) (@one_cat_shear_family_component_path B C C1 Prod
  t A T0 X b)) (@additive_shear_left_path C Prod t A (@fapp0 B C X b))) (@eq_trans (Hom C (@fapp0 (Product_cat C
  C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
  (@fapp0 B C X b) (@fapp0 B C X b)))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C
  X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_shear_family B C C1 Prod t A T0 X)) (@additive_shear_inverse C Prod t A (@fapp0 B C X
  b))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@additive_shear C Prod t A (@fapp0 B C X b))
  (@additive_shear_inverse C Prod t A (@fapp0 B C X b))) (@id C (@fapp0 (Product_cat C C) C Prod (@Product_pair
  C C (@fapp0 B C X b) (@fapp0 B C X b)))) (@eq_ap (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0
  B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))))
  (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat
  C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))) (λ h : τ (Hom C (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B
  C X b) (@fapp0 B C X b)))), (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b)
  (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) h (@additive_shear_inverse C
  Prod t A (@fapp0 B C X b)))) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_shear_family B C C1 Prod t
  A T0 X)) (@additive_shear C Prod t A (@fapp0 B C X b)) (@one_cat_shear_family_component_path B C C1 Prod
  t A T0 X b)) (@additive_shear_right_path C Prod t A (@fapp0 B C X b)));

// Existing generic whole inverse assembly applies to the already constructed S.
symbol one_cat_shear_family_omega [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X : τ (Functor B C))
  : τ (@OmegaEquivAlong (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A
  T0 X))
≔ @strict_transf_pointwise_omega_along B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A
  T0 X)
    (λ b : τ (Obj B), @one_cat_shear_family_component_omega B C C1 Prod t A T0 X b);

// Select the whole inverse from that same fixed-forward evidence.
symbol one_cat_shear_family_inverse [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X : τ (Functor B C))
  : τ (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat
  C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X X)))
≔ @omega_equiv_along_left_inv (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A
  T0 X) (@one_cat_shear_family_omega B C C1 Prod t A T0 X);
