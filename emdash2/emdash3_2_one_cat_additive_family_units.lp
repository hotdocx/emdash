require open emdash.emdash3_2_one_cat_copair_injection_paths;
require open emdash.emdash3_2_one_cat_difference_family_bilinearity;
require open emdash.emdash3_2_one_cat_kernel_pullback_lifts;
require open emdash.emdash3_2_one_cat_zero_family_postcomposition_paths;

// The original pairing with zero factors through the original whole first injection.
symbol one_cat_product_pair_zero_second_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B C X Y))
 : τ (@= (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y Y f
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y)) (@comp_fapp0 (Functor_cat
  B C) X Y (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C
  Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) (@one_cat_product_family_pair B C
  C1 Prod (@additive_binary_products C Prod t A) Y Y Y (@id (Functor_cat B C) Y) (@zero_arrow_family_zero_transf B
  C t (@additive_terminal_object C Prod t A) T0 Y Y)) f))
≔ (@eq_sym _ _ _ (@eq_trans _ _ _ _ (@one_cat_product_pair_precompose_path B C C1 Prod (@additive_binary_products
  C Prod t A) X Y Y Y f (@id (Functor_cat B C) Y) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object
  C Prod t A) T0 Y Y)) (@eq_ap (@Transf B C X Y) (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) Y Y))) (λ g : τ (@Transf B C X Y), (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f g)) (@comp_fapp0 (Functor_cat B C) X Y Y
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y Y) f)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y)
  (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0 X Y Y f))));

// The whole coproduct injection law and native pairing give f+0=f.
symbol one_cat_additive_family_right_zero_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B C X Y))
 : τ (@= (@Transf B C X Y) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@zero_arrow_family_zero_transf
  B C t (@additive_terminal_object C Prod t A) T0 X Y)) f)
≔ (@eq_trans _ _ _ _ (@one_cat_additive_family_add_formula_path B C C1 Prod t A T0 X Y f
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y)) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y) (@Transf B C X Y) (λ h : τ
  (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y), (@comp_fapp0 (Functor_cat B
  C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y h (@one_cat_product_family_pair B C C1
  Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X))))
  (@one_cat_copair_family B C C1 Prod t A T0 X X Y f (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y)) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) Y Y)) Y (@one_cat_copair_family B C C1 Prod t A T0 Y Y Y (@id (Functor_cat B C) Y) (@id (Functor_cat B C) Y))
  (@product_family_map B C Prod X X Y Y f (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod
  t A) T0 X Y))) (@eq_sym _ _ _ (@one_cat_copair_source_path B C C1 Prod t A T0 X X Y Y Y f
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y) (@id (Functor_cat B C) Y)
  (@id (Functor_cat B C) Y)))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) Y Y)) Y (@one_cat_copair_family B C C1 Prod t A T0 Y Y Y (@id (Functor_cat B C) Y)
  (@id (Functor_cat B C) Y)) (@product_family_map B C Prod X X Y Y f (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)))) (@eq_trans _
  _ _ _ (@eq_ap (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y))) (@Transf B C
  X Y) (λ h : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y))), (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y
  (@one_cat_copair_family B C C1 Prod t A T0 Y Y Y (@id (Functor_cat B C) Y) (@id (Functor_cat B C) Y)) h))
  (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) (@product_family_map B C Prod X X Y Y f
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X)
  (@id (Functor_cat B C) X))) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X Y
  Y f (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y))
  (@one_cat_product_pair_target_path B C C1 Prod (@additive_binary_products C Prod t A) X X X Y Y (@id
  (Functor_cat B C) X) (@id (Functor_cat B C) X) f (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C X (@fapp0 (Functor_cat
  B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) Y Y))) (@Transf B C X Y) (λ h : τ (@Transf B C X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) Y Y))), (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y (@one_cat_copair_family B C C1 Prod t A T0 Y Y Y (@id
  (Functor_cat B C) Y) (@id (Functor_cat B C) Y)) h)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X Y Y f (@zero_arrow_family_zero_transf B C t (@additive_terminal_object
  C Prod t A) T0 X Y)) (@comp_fapp0 (Functor_cat B C) X Y (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor
  B C) Y Y)) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) Y Y Y (@id
  (Functor_cat B C) Y) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y Y)) f)
  (@one_cat_product_pair_zero_second_path B C C1 Prod t A T0 X Y f)) (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat B C) X Y (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y
  (@one_cat_copair_family B C C1 Prod t A T0 Y Y Y (@id (Functor_cat B C) Y) (@id (Functor_cat B C) Y))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) Y Y Y (@id (Functor_cat B C) Y)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y Y)) f) (@eq_ap (@Transf B C Y
  Y) (@Transf B C X Y) (λ h : τ (@Transf B C Y Y), (@comp_fapp0 (Functor_cat B C) X Y Y h f)) (@comp_fapp0
  (Functor_cat B C) Y (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) Y Y)) Y
  (@one_cat_copair_family B C C1 Prod t A T0 Y Y Y (@id (Functor_cat B C) Y) (@id (Functor_cat B C) Y))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) Y Y Y (@id (Functor_cat B C) Y)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y Y))) (@id (Functor_cat B C) Y)
  (@one_cat_copair_first_injection_path B C C1 Prod t A T0 Y Y Y (@id (Functor_cat B C) Y) (@id (Functor_cat B C)
  Y)))))))));

// Whole negation preserves zero through its original postcomposition formula.
symbol one_cat_negative_family_zero_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y : τ (Functor B C))
 : τ (@= (@Transf B C X Y) (@one_cat_negative_family B C C1 Prod t A T0 X Y (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object
  C Prod t A) T0 X Y))
≔ (@eq_trans _ _ _ _ (@one_cat_negative_family_formula_path B C C1 Prod t A T0 X Y (@zero_arrow_family_zero_transf
  B C t (@additive_terminal_object C Prod t A) T0 X Y)) (@one_cat_zero_family_postcompose_path B C C1 t
  (@additive_terminal_object C Prod t A) T0 X Y Y (@one_cat_negative_family_transf B C C1 Prod t A T0 Y)));

// The original whole difference now satisfies f−0=f.
symbol one_cat_difference_family_right_zero_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
  τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B C X Y))
 : τ (@= (@Transf B C X Y) (@one_cat_difference_family B C C1 Prod t A T0 X Y f (@zero_arrow_family_zero_transf B
  C t (@additive_terminal_object C Prod t A) T0 X Y)) f)
≔ (@eq_trans _ _ _ _ (@one_cat_difference_family_formula_path B C C1 Prod t A T0 X Y f
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y)) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf B C X Y) (@Transf B C X Y) (λ g : τ (@Transf B C X Y), (@one_cat_additive_family_add B C C1 Prod t A T0
  X Y f g)) (@one_cat_negative_family B C C1 Prod t A T0 X Y (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object
  C Prod t A) T0 X Y) (@one_cat_negative_family_zero_path B C C1 Prod t A T0 X Y))
  (@one_cat_additive_family_right_zero_path B C C1 Prod t A T0 X Y f)));

// A whole map killing the correction preserves the original first map after subtraction.
symbol one_cat_difference_killed_second_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y : τ (Functor B C)) (Z : τ (Functor B C)) (f g : τ (@Transf B C X Y)) (h : τ (@Transf B C Y
  Z)) (e : τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z h g) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Z)))
 : τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_difference_family B C C1 Prod t A T0 X
  Y f g)) (@comp_fapp0 (Functor_cat B C) X Y Z h f))
≔ (@eq_trans _ _ _ _ (@one_cat_difference_family_postcompose_path B C C1 Prod t A T0 X Y Z f g h) (@eq_trans _ _ _
  _ (@eq_ap (@Transf B C X Z) (@Transf B C X Z) (λ k : τ (@Transf B C X Z), (@one_cat_difference_family B C C1
  Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f) k)) (@comp_fapp0 (Functor_cat B C) X Y Z h g)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Z) e)
  (@one_cat_difference_family_right_zero_path B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h
  f))));
