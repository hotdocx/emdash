/* Whole negative identity extracted from the inverse of the native shear. */
require open emdash.emdash3_2_one_cat_shear_families;
require open emdash.emdash3_2_preadditive_zero_family_components;
require open emdash.emdash3_2_eq1_evidence_property;

// The original whole injection is the product mate of id and canonical zero.
symbol one_cat_double_family_inj1 [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X : τ (Functor B C)) : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)))
≔ @one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X X);

// Its point agrees with the original additive injection.
symbol one_cat_double_family_inj1_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X : τ (Functor B C)) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X
  b)))) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) b
  (@one_cat_double_family_inj1 B C C1 Prod t A T0 X)) (@additive_inj1_fapp0 C Prod t A (@fapp0 B C X b) (@fapp0
  B C X b)))
≔ @eq_trans (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X
  b)))) _ _ _
    (@one_cat_product_family_pair_component_path B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id
  (Functor_cat B C) X) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X X) b)
    (@binary_products_pair_right_path C Prod (@additive_binary_products C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b)
  (@fapp0 B C X b) (@id C (@fapp0 B C X b)) _ (@preadditive_hom_zero C (@additive_preadditive C Prod t A) (@fapp0 B C
  X b) (@fapp0 B C X b))
      (@preadditive_zero_family_component_path B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 X X b));

// The whole inverse keeps the original selected scalar inverse computationally visible.
symbol one_cat_shear_family_inverse_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X : τ (Functor B C)) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_shear_family_inverse B C C1 Prod t A T0 X)) (@additive_shear_inverse C Prod t A (@fapp0
  B C X b)))
≔ @eq_refl (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))) (@additive_shear_inverse C
  Prod t A (@fapp0 B C X b));

// −id_X = (π₂∘S_X⁻¹)∘ι₁, using only whole categorical operations.
symbol one_cat_shear_negative_identity_family [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X : τ (Functor B C)) : τ (@Transf B C X X)
≔ (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X)
  (@one_cat_shear_family_inverse B C C1 Prod t A T0 X)) (@one_cat_double_family_inj1 B C C1 Prod t A T0
  X));

// Point equality is an observation of the already built whole negative identity.
symbol one_cat_shear_negative_identity_family_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ
  (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C X b)) (@tapp0_fapp0 B C X X b
  (@one_cat_shear_negative_identity_family B C C1 Prod t A T0 X)) (@preadditive_hom_neg C (@additive_preadditive
  C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b) (@id C (@fapp0 B C X b))))
≔ (@eq_trans (Hom C (@fapp0 B C X b) (@fapp0 B C X b)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C
  Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b) (@comp_fapp0 C (@fapp0 (Product_cat C
  C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
  (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X b (@one_cat_double_family_proj2 B C C1 Prod t A X)) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_shear_family_inverse B C C1 Prod t A T0 X))) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_double_family_inj1 B C C1 Prod t A T0 X))) (@comp_fapp0 C
  (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C
  X b) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b)
  (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b))
  (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_shear_family_inverse B C C1 Prod t A T0 X))) (@tapp0_fapp0
  B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_double_family_inj1 B C C1
  Prod t A T0 X))) (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b) (@id C
  (@fapp0 B C X b))) (@eq_ap (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X
  b))) (@fapp0 B C X b)) (Hom C (@fapp0 B C X b) (@fapp0 B C X b)) (λ h : τ (Hom C (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b)), (@comp_fapp0 C (@fapp0 B C X b) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b) (@comp_fapp0 C
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C
  Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b) h (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_shear_family_inverse B C C1 Prod t A T0 X))) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_double_family_inj1 B C C1 Prod t A T0 X)))) (@tapp0_fapp0
  B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X b (@one_cat_double_family_proj2 B C
  C1 Prod t A X)) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) (@fapp0 B C X b) (@fapp0
  B C X b)) (@one_cat_double_family_proj2_component_path B C C1 Prod t A X b)) (@eq_trans (Hom C (@fapp0 B C X
  b) (@fapp0 B C X b)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C
  X b) (@fapp0 B C X b))) (@fapp0 B C X b) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0
  B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))
  (@fapp0 B C X b) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) (@fapp0 B C X b)
  (@fapp0 B C X b)) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_shear_family_inverse B C C1 Prod t A T0
  X))) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) b
  (@one_cat_double_family_inj1 B C C1 Prod t A T0 X))) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C)
  C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b) (@comp_fapp0 C (@fapp0 (Product_cat C
  C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
  (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products
  C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b)) (@additive_shear_inverse C Prod t A (@fapp0 B C X b)))
  (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) b
  (@one_cat_double_family_inj1 B C C1 Prod t A T0 X))) (@preadditive_hom_neg C (@additive_preadditive C Prod t
  A) (@fapp0 B C X b) (@fapp0 B C X b) (@id C (@fapp0 B C X b))) (@eq_ap (Hom C (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B
  C X b) (@fapp0 B C X b)))) (Hom C (@fapp0 B C X b) (@fapp0 B C X b)) (λ h : τ (Hom C (@fapp0 (Product_cat C C) C
  Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
  (@fapp0 B C X b) (@fapp0 B C X b)))), (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b) (@comp_fapp0 C (@fapp0 (Product_cat C C) C
  Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
  (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products
  C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b)) h) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) b (@one_cat_double_family_inj1 B C C1 Prod t A T0 X)))) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_shear_family_inverse B C C1 Prod t A T0 X)) (@additive_shear_inverse C Prod t A (@fapp0
  B C X b)) (@one_cat_shear_family_inverse_component_path B C C1 Prod t A T0 X b)) (@eq_trans (Hom C (@fapp0 B C
  X b) (@fapp0 B C X b)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B
  C X b) (@fapp0 B C X b))) (@fapp0 B C X b) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
  (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C
  X b))) (@fapp0 B C X b) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) (@fapp0 B C X b)
  (@fapp0 B C X b)) (@additive_shear_inverse C Prod t A (@fapp0 B C X b))) (@tapp0_fapp0 B C X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_double_family_inj1 B C C1 Prod t A T0
  X))) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B
  C X b))) (@fapp0 B C X b) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b)
  (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B
  C X b) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) (@fapp0 B C X b) (@fapp0 B C X
  b)) (@additive_shear_inverse C Prod t A (@fapp0 B C X b))) (@additive_inj1_fapp0 C Prod t A (@fapp0 B C X b)
  (@fapp0 B C X b))) (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b) (@id
  C (@fapp0 B C X b))) (@eq_ap (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C
  X b) (@fapp0 B C X b)))) (Hom C (@fapp0 B C X b) (@fapp0 B C X b)) (λ h : τ (Hom C (@fapp0 B C X b) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))), (@comp_fapp0 C (@fapp0 B C X b)
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b)
  (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C X b)
  (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b))
  (@additive_shear_inverse C Prod t A (@fapp0 B C X b))) h)) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_double_family_inj1 B C C1 Prod t A T0 X))
  (@additive_inj1_fapp0 C Prod t A (@fapp0 B C X b) (@fapp0 B C X b))
  (@one_cat_double_family_inj1_component_path B C C1 Prod t A T0 X b))
  (@additive_shear_inverse_negative_projection_path C Prod t A (@fapp0 B C X b)))));

// One universal negative identity; restriction uses the existing generic action.
symbol one_cat_negative_identity_transf [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) :
  τ (@Transf C C (@id_func C) (@id_func C))
≔ @one_cat_shear_negative_identity_family C C C1 Prod t A T0 (@id_func C);

// The universal transfor computes to the original −id at each object.
symbol one_cat_negative_identity_component_path [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (x : τ (Obj C))
  : τ (@= (Hom C x x) (@tapp0_fapp0 C C (@id_func C) (@id_func C) x (@one_cat_negative_identity_transf C C1 Prod
  t A T0))
      (@preadditive_hom_neg C (@additive_preadditive C Prod t A) x x (@id C x)))
≔ @one_cat_shear_negative_identity_family_component_path C C C1 Prod t A T0 (@id_func C) x;
