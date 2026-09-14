require open emdash.emdash3_2_one_cat_additive_family_inverse;
require open emdash.emdash3_2_omega_equiv_cancellation_paths;
require open emdash.emdash3_2_one_cat_difference_family_bilinearity;

/* Whole addition cancellation is inherited from the original invertible shear. */

// The whole shear acts on a pair by (f,g)↦(f,f+g).
symbol one_cat_shear_pair_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X Y : τ (Functor B C))
  (f g : τ (@Transf B C X Y))
  : τ (@= (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) (@one_cat_shear_family B C C1 Prod t A T0 Y) (@one_cat_product_family_pair B
  C C1 Prod (@additive_binary_products C Prod t A) X Y Y f g)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f g)))
≔ (@eq_trans (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) (@one_cat_shear_family B C C1 Prod t A T0 Y) (@one_cat_product_family_pair B
  C C1 Prod (@additive_binary_products C Prod t A) X Y Y f g)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj1 B C C1 Prod t A Y) (@one_cat_product_family_pair B C C1
  Prod (@additive_binary_products C Prod t A) X Y Y f g)) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj1 B C C1 Prod t A Y)
  (@one_cat_double_family_proj2 B C C1 Prod t A Y)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f g))) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f g))
  (@one_cat_product_pair_precompose_path B C C1 Prod (@additive_binary_products C Prod t A) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) Y Y (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C
  Prod t A) X Y Y f g) (@one_cat_double_family_proj1 B C C1 Prod t A Y) (@one_cat_additive_family_add B C C1 Prod t A
  T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj1 B C C1 Prod
  t A Y) (@one_cat_double_family_proj2 B C C1 Prod t A Y))) (@eq_trans (@Transf B C X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y))) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod
  t A) X Y Y (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y
  Y)) Y (@one_cat_double_family_proj1 B C C1 Prod t A Y) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f g)) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj1 B C C1 Prod t A Y)
  (@one_cat_double_family_proj2 B C C1 Prod t A Y)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f g))) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat
  C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) Y Y)) Y (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj1 B C C1 Prod t A Y)
  (@one_cat_double_family_proj2 B C C1 Prod t A Y)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f g))) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f g)) (@eq_ap
  (@Transf B C X Y) (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y))) (λ h : τ (@Transf
  B C X Y), (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y h (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_additive_family_add B
  C C1 Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj1 B C
  C1 Prod t A Y) (@one_cat_double_family_proj2 B C C1 Prod t A Y)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f g)))) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj1 B C C1 Prod t A Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y f g)) f
  (@one_cat_product_family_pair_proj1_path B C C1 Prod (@additive_binary_products C Prod t A) X Y Y f g)) (@eq_ap
  (@Transf B C X Y) (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y))) (λ h : τ (@Transf
  B C X Y), (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y f h)) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_additive_family_add B
  C C1 Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj1 B C
  C1 Prod t A Y) (@one_cat_double_family_proj2 B C C1 Prod t A Y)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f g)) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f g)
  (@eq_trans (@Transf B C X Y) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) Y Y)) Y (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  Y Y)) Y (@one_cat_double_family_proj1 B C C1 Prod t A Y) (@one_cat_double_family_proj2 B C C1 Prod t A Y))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y f g))
  (@one_cat_additive_family_add B C C1 Prod t A T0 X Y (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj1 B C C1 Prod t A Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y f g)) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj2 B
  C C1 Prod t A Y) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y f g)))
  (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f g) (@one_cat_additive_family_precompose_path B C C1 Prod t A
  T0 X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj1 B C C1 Prod
  t A Y) (@one_cat_double_family_proj2 B C C1 Prod t A Y) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f g)) (@eq_trans (@Transf B C X Y) (@one_cat_additive_family_add B C C1
  Prod t A T0 X Y (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y
  Y)) Y (@one_cat_double_family_proj1 B C C1 Prod t A Y) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f g)) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj2 B C C1 Prod t A Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y f g)))
  (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj2 B C C1 Prod t A Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y f g)))
  (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f g) (@eq_ap (@Transf B C X Y) (@Transf B C X Y) (λ h : τ
  (@Transf B C X Y), (@one_cat_additive_family_add B C C1 Prod t A T0 X Y h (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj2 B C C1 Prod t A Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y f g)))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj1 B
  C C1 Prod t A Y) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y f g)) f
  (@one_cat_product_family_pair_proj1_path B C C1 Prod (@additive_binary_products C Prod t A) X Y Y f g)) (@eq_ap
  (@Transf B C X Y) (@Transf B C X Y) (λ h : τ (@Transf B C X Y), (@one_cat_additive_family_add B C C1 Prod t A T0 X Y
  f h)) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y
  Y)) Y (@one_cat_double_family_proj2 B C C1 Prod t A Y) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f g)) g (@one_cat_product_family_pair_proj2_path B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f g)))))));

// A common left summand cancels using the same whole shear equivalence.
symbol one_cat_additive_family_left_cancel [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y : τ (Functor B C))
  (a b c : τ (@Transf B C X Y))
  (p : τ (@= (@Transf B C X Y) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y a b) (@one_cat_additive_family_add
  B C C1 Prod t A T0 X Y a c)))
  : τ (@= (@Transf B C X Y) b c)
≔ (@eq_trans (@Transf B C X Y) b (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) Y Y)) Y (@one_cat_double_family_proj2 B C C1 Prod t A Y) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y a b)) c (@eq_sym (@Transf B C X Y) (@comp_fapp0 (Functor_cat B C) X
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj2 B C C1 Prod
  t A Y) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y a b)) b
  (@one_cat_product_family_pair_proj2_path B C C1 Prod (@additive_binary_products C Prod t A) X Y Y a b)) (@eq_trans
  (@Transf B C X Y) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y
  Y)) Y (@one_cat_double_family_proj2 B C C1 Prod t A Y) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y a b)) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj2 B C C1 Prod t A Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y a c)) c (@eq_ap (@Transf B C
  X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y))) (@Transf B C X Y) (λ h : τ (@Transf B C X
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y))), (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_double_family_proj2 B C C1 Prod t A Y) h))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y a b)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y a c)
  (@omega_equiv_postcomp_reflect_path (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y
  Y)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) (@one_cat_shear_family B C C1 Prod t A T0 Y)
  (@one_cat_shear_family_omega B C C1 Prod t A T0 Y) X (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y a b) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y a c) (@eq_trans (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) Y Y))) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  Y Y)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) (@one_cat_shear_family B C C1 Prod t A T0 Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y a b))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y a
  (@one_cat_additive_family_add B C C1 Prod t A T0 X Y a b)) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y
  Y)) (@one_cat_shear_family B C C1 Prod t A T0 Y) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y a c)) (@one_cat_shear_pair_path B C C1 Prod t A T0 X Y a b)
  (@eq_trans (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y a
  (@one_cat_additive_family_add B C C1 Prod t A T0 X Y a b)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y a (@one_cat_additive_family_add B C C1 Prod t A T0 X Y a c))
  (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) (@one_cat_shear_family B C C1 Prod t A T0 Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y a c)) (@eq_ap (@Transf B C X
  Y) (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y))) (λ h : τ (@Transf B C X Y),
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y a h))
  (@one_cat_additive_family_add B C C1 Prod t A T0 X Y a b) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y a c)
  p) (@eq_sym (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) Y Y)) (@one_cat_shear_family B C C1 Prod t A T0 Y) (@one_cat_product_family_pair B
  C C1 Prod (@additive_binary_products C Prod t A) X Y Y a c)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y a (@one_cat_additive_family_add B C C1 Prod t A T0 X Y a c))
  (@one_cat_shear_pair_path B C C1 Prod t A T0 X Y a c)))))) (@one_cat_product_family_pair_proj2_path B C C1
  Prod (@additive_binary_products C Prod t A) X Y Y a c)));

/* Cancellability of original whole negation, using its existing component interpretation. */

// Original scalar −id is its own inverse under composition.
symbol preadditive_negative_identity_square_path [C : Cat] (S : τ (@PreadditiveCategory C)) (x : τ (Obj C))
  : τ (@= (Hom C x x)
      (@comp_fapp0 C x x x (@preadditive_hom_neg C S x x (@id C x)) (@preadditive_hom_neg C S x x (@id C x))) (@id C
  x))
≔ @eq_trans (Hom C x x) _ _ _
    (@preadditive_comp_neg_left_path C S x x x (@id C x) (@preadditive_hom_neg C S x x (@id C x)))
    (@abelian_group_neg_involutive_path (Hom C x x) (@preadditive_hom_structure C S x x) (@id C x));

// Fix the actual component while retaining the original scalar inverse in both slots.
symbol one_cat_negative_identity_component_omega [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (x : τ (Obj C))
  : τ (@OmegaEquivAlong C x x (@tapp0_fapp0 C C (@id_func C) (@id_func C) x (@one_cat_negative_identity_transf C C1
  Prod t A T0)))
≔ @omega_equiv_along_intro C x x (@tapp0_fapp0 C C (@id_func C) (@id_func C) x (@one_cat_negative_identity_transf C C1
  Prod t A T0)) (@preadditive_hom_neg C (@additive_preadditive C Prod t A) x x (@id C x)) (@preadditive_hom_neg C
  (@additive_preadditive C Prod t A) x x (@id C x)) (@eq_trans (Hom C x x) (@comp_fapp0 C x x x (@preadditive_hom_neg
  C (@additive_preadditive C Prod t A) x x (@id C x)) (@tapp0_fapp0 C C (@id_func C) (@id_func C) x
  (@one_cat_negative_identity_transf C C1 Prod t A T0))) (@comp_fapp0 C x x x (@preadditive_hom_neg C
  (@additive_preadditive C Prod t A) x x (@id C x)) (@preadditive_hom_neg C (@additive_preadditive C Prod t A) x x
  (@id C x))) (@id C x) (@eq_ap (Hom C x x) (Hom C x x) (λ h : τ (Hom C x x), (@comp_fapp0 C x x x
  (@preadditive_hom_neg C (@additive_preadditive C Prod t A) x x (@id C x)) h)) (@tapp0_fapp0 C C (@id_func C)
  (@id_func C) x (@one_cat_negative_identity_transf C C1 Prod t A T0)) (@preadditive_hom_neg C (@additive_preadditive
  C Prod t A) x x (@id C x)) (@one_cat_negative_identity_component_path C C1 Prod t A T0 x))
  (@preadditive_negative_identity_square_path C (@additive_preadditive C Prod t A) x)) (@eq_trans (Hom C x x)
  (@comp_fapp0 C x x x (@tapp0_fapp0 C C (@id_func C) (@id_func C) x (@one_cat_negative_identity_transf C C1 Prod t A
  T0)) (@preadditive_hom_neg C (@additive_preadditive C Prod t A) x x (@id C x))) (@comp_fapp0 C x x x
  (@preadditive_hom_neg C (@additive_preadditive C Prod t A) x x (@id C x)) (@preadditive_hom_neg C
  (@additive_preadditive C Prod t A) x x (@id C x))) (@id C x) (@eq_ap (Hom C x x) (Hom C x x) (λ h : τ (Hom C x x),
  (@comp_fapp0 C x x x h (@preadditive_hom_neg C (@additive_preadditive C Prod t A) x x (@id C x)))) (@tapp0_fapp0 C C
  (@id_func C) (@id_func C) x (@one_cat_negative_identity_transf C C1 Prod t A T0)) (@preadditive_hom_neg C
  (@additive_preadditive C Prod t A) x x (@id C x)) (@one_cat_negative_identity_component_path C C1 Prod t A T0 x))
  (@preadditive_negative_identity_square_path C (@additive_preadditive C Prod t A) x));

// Existing generic pointwise-to-whole inversion applies to the already formed universal N.
symbol one_cat_negative_identity_omega [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  : τ (@OmegaEquivAlong (Functor_cat C C) (@id_func C) (@id_func C) (@one_cat_negative_identity_transf C C1 Prod t A
  T0))
≔ @strict_transf_pointwise_omega_along C C (@id_func C) (@id_func C) (@one_cat_negative_identity_transf C C1 Prod t A
  T0)
    (λ x : τ (Obj C), @one_cat_negative_identity_component_omega C C1 Prod t A T0 x);

// Restrict that same fixed-forward evidence along the original family.
symbol one_cat_negative_family_omega [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Y : τ (Functor B C))
  : τ (@OmegaEquivAlong (Functor_cat B C) Y Y (@one_cat_negative_family_transf B C C1 Prod t A T0 Y))
≔ @omega_equiv_along_fapp1_fapp0 (Functor_cat C C) (Functor_cat B C) (@comp_cat_con_func B C C Y)
    (@id_func C) (@id_func C) (@one_cat_negative_identity_transf C C1 Prod t A T0)
  (@one_cat_negative_identity_omega C C1 Prod t A T0);

// Negation reflects equality of whole transformations through that original equivalence.
symbol one_cat_negative_family_reflect_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y : τ (Functor B C))
  (f g : τ (@Transf B C X Y)) (p : τ (@= (@Transf B C X Y) (@one_cat_negative_family B C C1 Prod t A T0 X Y f)
  (@one_cat_negative_family B C C1 Prod t A T0 X Y g)))
  : τ (@= (@Transf B C X Y) f g)
≔ @omega_equiv_postcomp_reflect_path (Functor_cat B C) Y Y (@one_cat_negative_family_transf B C C1 Prod t A T0 Y)
    (@one_cat_negative_family_omega B C C1 Prod t A T0 Y) X f g (@eq_trans (@Transf B C X Y) (@comp_fapp0
  (Functor_cat B C) X Y Y (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f) (@one_cat_negative_family B C C1
  Prod t A T0 X Y f) (@comp_fapp0 (Functor_cat B C) X Y Y (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) g)
  (@eq_sym (@Transf B C X Y) (@one_cat_negative_family B C C1 Prod t A T0 X Y f) (@comp_fapp0 (Functor_cat B C) X Y Y
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f) (@one_cat_negative_family_formula_path B C C1 Prod t A T0
  X Y f)) (@eq_trans (@Transf B C X Y) (@one_cat_negative_family B C C1 Prod t A T0 X Y f) (@one_cat_negative_family B
  C C1 Prod t A T0 X Y g) (@comp_fapp0 (Functor_cat B C) X Y Y (@one_cat_negative_family_transf B C C1 Prod t A T0 Y)
  g) p (@one_cat_negative_family_formula_path B C C1 Prod t A T0 X Y g)));

// A zero whole difference implies equality, without assuming a full additive capability.
symbol one_cat_difference_family_zero_reflect [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y : τ (Functor B C))
  (f g : τ (@Transf B C X Y)) (p : τ (@= (@Transf B C X Y) (@one_cat_difference_family B C C1 Prod t A T0 X Y f g)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y)))
  : τ (@= (@Transf B C X Y) f g)
≔ @eq_sym (@Transf B C X Y) g f (@one_cat_negative_family_reflect_path B C C1 Prod t A T0 X Y g f
  (@one_cat_additive_family_left_cancel B C C1 Prod t A T0 X Y f (@one_cat_negative_family B C C1 Prod t A T0 X
  Y g) (@one_cat_negative_family B C C1 Prod t A T0 X Y f) (@eq_trans (@Transf B C X Y) (@one_cat_additive_family_add
  B C C1 Prod t A T0 X Y f (@one_cat_negative_family B C C1 Prod t A T0 X Y g)) (@one_cat_difference_family B C C1
  Prod t A T0 X Y f g) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@one_cat_negative_family B C C1 Prod t
  A T0 X Y f)) (@eq_sym (@Transf B C X Y) (@one_cat_difference_family B C C1 Prod t A T0 X Y f g)
  (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@one_cat_negative_family B C C1 Prod t A T0 X Y g))
  (@one_cat_difference_family_formula_path B C C1 Prod t A T0 X Y f g)) (@eq_trans (@Transf B C X Y)
  (@one_cat_difference_family B C C1 Prod t A T0 X Y f g) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f
  (@one_cat_negative_family B C C1 Prod t A T0 X Y f)) p (@eq_sym (@Transf B C X Y) (@one_cat_additive_family_add B C
  C1 Prod t A T0 X Y f (@one_cat_negative_family B C C1 Prod t A T0 X Y f)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y) (@one_cat_additive_family_inverse_path B C C1 Prod t A T0 X Y
  f))))));

/* Consequences for the original whole negative identity and difference operation. */

// The directly assembled shear negative and original restriction agree wholly.
symbol one_cat_negative_family_shear_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X : τ (Functor B C))
  : τ (@= (@Transf B C X X) (@one_cat_shear_negative_identity_family B C C1 Prod t A T0 X)
  (@one_cat_negative_family_transf B C C1 Prod t A T0 X))
≔ @one_cat_additive_family_left_cancel B C C1 Prod t A T0 X X (@id (Functor_cat B C) X)
  (@one_cat_shear_negative_identity_family B C C1 Prod t A T0 X) (@one_cat_negative_family_transf B C C1 Prod t A T0
  X) (@eq_trans (@Transf B C X X) (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@id (Functor_cat B C) X)
  (@one_cat_shear_negative_identity_family B C C1 Prod t A T0 X)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X X) (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@id
  (Functor_cat B C) X) (@one_cat_negative_family_transf B C C1 Prod t A T0 X))
  (@one_cat_shear_negative_identity_add_path B C C1 Prod t A T0 X) (@eq_sym (@Transf B C X X)
  (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@id (Functor_cat B C) X) (@one_cat_negative_family_transf B C
  C1 Prod t A T0 X)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X X)
  (@one_cat_negative_family_add_path B C C1 Prod t A T0 X)));

// Equal whole composites make the corresponding composed difference zero.
symbol one_cat_difference_family_precompose_zero_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (W X Y : τ (Functor B C)) (f g : τ (@Transf B C X Y)) (h : τ (@Transf B C W X))
  (p : τ (@= (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0 (Functor_cat B C) W X Y g h))) :
  τ (@= (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W X Y (@one_cat_difference_family B C C1 Prod t A T0 X Y f g)
  h) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 W Y))
≔ (@eq_trans (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W X Y (@one_cat_difference_family B C C1 Prod t A T0 X Y
  f g) h) (@one_cat_difference_family B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0
  (Functor_cat B C) W X Y g h)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 W Y)
  (@one_cat_difference_family_precompose_path B C C1 Prod t A T0 W X Y f g h) (@eq_trans (@Transf B C W Y)
  (@one_cat_difference_family B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0
  (Functor_cat B C) W X Y g h)) (@one_cat_difference_family B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X
  Y g h) (@comp_fapp0 (Functor_cat B C) W X Y g h)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 W Y) (@eq_ap (@Transf B C W Y) (@Transf B C W Y) (λ u : τ (@Transf B C W Y),
  (@one_cat_difference_family B C C1 Prod t A T0 W Y u (@comp_fapp0 (Functor_cat B C) W X Y g h))) (@comp_fapp0
  (Functor_cat B C) W X Y f h) (@comp_fapp0 (Functor_cat B C) W X Y g h) p)
  (@one_cat_difference_family_self_path B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y g h))));

// Equal whole composites make the corresponding composed difference zero.
symbol one_cat_difference_family_postcompose_zero_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f g : τ (@Transf B C X Y)) (h : τ (@Transf B C Y Z))
  (p : τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@comp_fapp0 (Functor_cat B C) X Y Z h g))) :
  τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_difference_family B C C1 Prod t A T0 X Y f
  g)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Z))
≔ (@eq_trans (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_difference_family B C C1 Prod t A T0 X
  Y f g)) (@one_cat_difference_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@comp_fapp0
  (Functor_cat B C) X Y Z h g)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Z)
  (@one_cat_difference_family_postcompose_path B C C1 Prod t A T0 X Y Z f g h) (@eq_trans (@Transf B C X Z)
  (@one_cat_difference_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@comp_fapp0
  (Functor_cat B C) X Y Z h g)) (@one_cat_difference_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y
  Z h g) (@comp_fapp0 (Functor_cat B C) X Y Z h g)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 X Z) (@eq_ap (@Transf B C X Z) (@Transf B C X Z) (λ u : τ (@Transf B C X Z),
  (@one_cat_difference_family B C C1 Prod t A T0 X Z u (@comp_fapp0 (Functor_cat B C) X Y Z h g))) (@comp_fapp0
  (Functor_cat B C) X Y Z h f) (@comp_fapp0 (Functor_cat B C) X Y Z h g) p)
  (@one_cat_difference_family_self_path B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h g))));
