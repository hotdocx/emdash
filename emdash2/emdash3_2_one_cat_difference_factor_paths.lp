require open emdash.emdash3_2_one_cat_difference_cospans;

// A factor through the first projection annihilates the original second leg.
symbol one_cat_difference_cospan_second_from_factor_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ
  (@TerminalObject (Op_cat C) t)) (X Y Z V : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z))
  (h : τ (@Transf B C Z V)) (a : τ (@Transf B C X V)) (p : τ (@= (@Transf B C (@fapp0 (Functor_cat B (Product_cat
  C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) V) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) Z V h (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)) (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X V a
  (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A) X Y))))
 : τ (@= (@Transf B C Y V) (@comp_fapp0 (Functor_cat B C) Y Z V h g) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 Y V))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@one_cat_difference_family_zero_reflect B C C1 Prod t A T0 Y V (@comp_fapp0
  (Functor_cat B C) Y Z V h (@comp_fapp0 (Functor_cat B C) Y X Z f (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 Y X))) (@comp_fapp0 (Functor_cat B C) Y Z V h g) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@one_cat_difference_cospan_postcompose_pair_path B C C1 Prod t A T0 X Y Z f g Y
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y X) (@id (Functor_cat B C) Y) V
  h)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) Y (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor
  B C) X Y)) Z V h (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g) (@one_cat_product_family_pair
  B C C1 Prod (@additive_binary_products C Prod t A) Y X Y (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 Y X) (@id (Functor_cat B C) Y))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B
  C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) V) (@Transf B C Y V) (λ b : τ (@Transf B
  C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) V), (@comp_fapp0 (Functor_cat B C) Y
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) V b (@one_cat_product_family_pair B C C1
  Prod (@additive_binary_products C Prod t A) Y X Y (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 Y X) (@id (Functor_cat B C) Y)))) (@comp_fapp0 (Functor_cat B C)
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z V h (@one_cat_difference_cospan_transf
  B C C1 Prod t A T0 X Y Z f g)) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) X V a (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A)
  X Y)) p) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) Y (@fapp0 (Functor_cat B (Product_cat
  C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) X V a (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C
  Prod t A) X Y) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) Y X Y
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y X) (@id (Functor_cat B C)
  Y)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C Y X) (@Transf B C Y V) (λ b : τ (@Transf B C Y X), (@comp_fapp0
  (Functor_cat B C) Y X V a b)) (@comp_fapp0 (Functor_cat B C) Y (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) X (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A) X
  Y) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) Y X Y
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y X) (@id (Functor_cat B C) Y)))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y X)
  (@one_cat_product_family_pair_proj1_path B C C1 Prod (@additive_binary_products C Prod t A) Y X Y
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y X) (@id (Functor_cat B C) Y)))
  (@one_cat_zero_family_postcompose_path B C C1 t (@additive_terminal_object C Prod t A) T0 Y X V a))))))))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C Y Z) (@Transf B C Y V) (λ b : τ (@Transf B C Y Z), (@comp_fapp0
  (Functor_cat B C) Y Z V h b)) (@comp_fapp0 (Functor_cat B C) Y X Z f (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 Y X)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object
  C Prod t A) T0 Y Z) (@one_cat_zero_family_postcompose_path B C C1 t (@additive_terminal_object C Prod t A) T0 Y
  X Z f)) (@one_cat_zero_family_postcompose_path B C C1 t (@additive_terminal_object C Prod t A) T0 Y Z V h)));

// The original first projection detects zero by its original whole injection.
symbol one_cat_product_first_zero_reflect_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y V : τ (Functor B C)) (a : τ (@Transf B C X V)) (z : τ (@= (@Transf B C (@fapp0 (Functor_cat
  B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) V) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) X V a (@one_cat_product_family_proj1 B C C1 Prod
  (@additive_binary_products C Prod t A) X Y)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) V)))
 : τ (@= (@Transf B C X V) a (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X V))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf B C X X) (@Transf B C X V) (λ b : τ (@Transf B C X X), (@comp_fapp0
  (Functor_cat B C) X X V a b)) (@id (Functor_cat B C) X) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) X (@one_cat_product_family_proj1 B C C1 Prod
  (@additive_binary_products C Prod t A) X Y) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products
  C Prod t A) X X Y (@id (Functor_cat B C) X) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 X Y))) (@eq_sym _ _ _ (@one_cat_product_family_pair_proj1_path B C C1 Prod
  (@additive_binary_products C Prod t A) X X Y (@id (Functor_cat B C) X) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y)))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X V a (@one_cat_product_family_proj1 B C
  C1 Prod (@additive_binary_products C Prod t A) X Y) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X X Y (@id (Functor_cat B C) X) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) V) (@Transf B C X V) (λ b : τ (@Transf B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) V), (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) V b (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X X Y (@id (Functor_cat B C) X) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y)))) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) X V a (@one_cat_product_family_proj1 B C C1 Prod
  (@additive_binary_products C Prod t A) X Y)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) V) z)
  (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0 X (@fapp0 (Functor_cat
  B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) V (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X X Y (@id (Functor_cat B C) X) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y))))));
