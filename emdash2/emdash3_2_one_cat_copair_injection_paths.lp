require open emdash.emdash3_2_one_cat_biproduct_injection_reindex;
require open emdash.emdash3_2_one_cat_biproduct_family_distribution;

// The original coproduct unit is restricted through its whole native Hom action.
symbol one_cat_copair_unit_reindex_hom_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (X Y : τ (Functor B C))
 : τ (@= (Functor (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@id_func (Product_cat C C))
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod)) (Hom_cat (Functor_cat B
  (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B
  (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))))
  (@comp_cat_con_fapp1_func B (Product_cat C C) (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X Y) (@id_func (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod)) (@Product_map_func (@Transf_cat (Product_cat C C) C (@Product_projL_func C C)
  Prod) (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor
  B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@Transf_cat (Product_cat C C) C (@Product_projR_func
  C C) Prod) (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B
  (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projL_func
  C C) Prod) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y) (@Product_projR_func C C) Prod)))
≔ @eq_refl (Functor (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@id_func (Product_cat C C))
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod)) (Hom_cat (Functor_cat B
  (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B
  (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))))
  (@comp_cat_con_fapp1_func B (Product_cat C C) (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X Y) (@id_func (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod));

// The first whole coordinate is the original restricted injection.
symbol one_cat_copair_unit_first_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (X Y : τ (Functor B C))
 : τ (@= (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (sigma_Fst (@fapp0 (Hom_cat (Functor_cat (Product_cat
  C C) (Product_cat C C)) (@id_func (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod)) (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) (Product_cat C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@id_func (Product_cat C C))
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod)) (@unit_adj_transf
  (Product_cat C C) C Prod (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t A T0)))) (@fapp0
  (@Transf_cat (Product_cat C C) C (@Product_projL_func C C) Prod) (@Transf_cat B C (@comp_cat_fapp0 B
  (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y) (@Product_projL_func C C) Prod) (@one_cat_biproduct_inj1 C C1 Prod t A T0)))
≔ (@eq_ap (Functor (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@id_func (Product_cat C C))
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod)) (Hom_cat (Functor_cat B
  (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B
  (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))))
  (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _
  : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) X Y))) (λ F : τ (Functor (Hom_cat (Functor_cat (Product_cat C C)
  (Product_cat C C)) (@id_func (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod)) (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)))), sigma_Fst (@fapp0 (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C
  C)) (@id_func (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func
  C) Prod)) (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C
  (Product_cat C C) (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor
  B C) X Y))) F (@unit_adj_transf (Product_cat C C) C Prod (@product_diagonal_func C)
  (@one_cat_biproduct_adjunction C C1 Prod t A T0)))) (@comp_cat_con_fapp1_func B (Product_cat C C) (Product_cat C
  C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@id_func (Product_cat C C))
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod)) (@Product_map_func
  (@Transf_cat (Product_cat C C) C (@Product_projL_func C C) Prod) (@Transf_cat B C (@comp_cat_fapp0 B
  (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y))) (@Transf_cat (Product_cat C C) C (@Product_projR_func C C) Prod) (@Transf_cat B C (@comp_cat_fapp0 B
  (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y) (@Product_projL_func C C) Prod) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projR_func C C) Prod))
  (@one_cat_copair_unit_reindex_hom_path B C C1 Prod t A T0 X Y));

// The whole unit retains its complete pair of original restricted injections.
symbol one_cat_copair_unit_reindex_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (X Y : τ (Functor B C))
 : τ (@= (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C
  (Product_cat C C) (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor
  B C) X Y)))) (@fapp0 (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@id_func (Product_cat C C))
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod)) (Hom_cat (Functor_cat B
  (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B
  (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))
  (@comp_cat_con_fapp1_func B (Product_cat C C) (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X Y) (@id_func (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod)) (@unit_adj_transf (Product_cat C C) C Prod (@product_diagonal_func C)
  (@one_cat_biproduct_adjunction C C1 Prod t A T0))) (@Struct_sigma (@Transf B C (@comp_cat_fapp0 B (Product_cat C
  C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y))) (λ _ : τ (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))), (@Transf B C (@comp_cat_fapp0 B
  (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)))) (@fapp0 (@Transf_cat (Product_cat C C) C (@Product_projL_func C C) Prod) (@Transf_cat B C
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projL_func C C) Prod) (@one_cat_biproduct_inj1 C C1 Prod t A
  T0)) (@fapp0 (@Transf_cat (Product_cat C C) C (@Product_projR_func C C) Prod) (@Transf_cat B C (@comp_cat_fapp0
  B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y) (@Product_projR_func C C) Prod) (@one_cat_biproduct_inj2 C C1 Prod t A T0))))
≔ (@eq_ap (Functor (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@id_func (Product_cat C C))
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod)) (Hom_cat (Functor_cat B
  (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B
  (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))) (Obj
  (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))) (λ F
  : τ (Functor (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@id_func (Product_cat C C))
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod)) (Hom_cat (Functor_cat B
  (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B
  (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))),
  @fapp0 (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@id_func (Product_cat C C)) (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod)) (Hom_cat (Functor_cat B (Product_cat C
  C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B (Product_cat C C)
  (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) F (@unit_adj_transf (Product_cat C C) C
  Prod (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t A T0))) (@comp_cat_con_fapp1_func B
  (Product_cat C C) (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)
  (@id_func (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C)
  Prod)) (@Product_map_func (@Transf_cat (Product_cat C C) C (@Product_projL_func C C) Prod) (@Transf_cat B C
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (@Transf_cat (Product_cat C C) C (@Product_projR_func C C) Prod) (@Transf_cat
  B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _
  : τ (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projL_func C C) Prod) (@comp_cat_con_fapp1_func B
  (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projR_func
  C C) Prod)) (@one_cat_copair_unit_reindex_hom_path B C C1 Prod t A T0 X Y));

// The first inverse-copair coordinate is composition with the original whole injection.
symbol one_cat_uncopair_first_formula [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (X Y : τ (Functor B C)) (Z : τ (Functor B C)) (h : τ (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) Z))
 : τ (@= (@Transf B C X Z) (sigma_Fst (@one_cat_uncopair_family B C C1 Prod t A T0 X Y Z h)) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z h
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X Y (@id (Functor_cat B C) X)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y))))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z)) (@Transf B C X Z) (λ v :
  τ (@Transf B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)
  (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z)), sigma_Fst v) (@one_cat_uncopair_family B
  C C1 Prod t A T0 X Y Z h) (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C)
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y))) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z) (@fapp0 _ _ (@comp_cat_cov_fapp1_func
  B C (Product_cat C C) (@product_diagonal_func C) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) h) (@fapp0 (Hom_cat (Functor_cat (Product_cat C C)
  (Product_cat C C)) (@id_func (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod)) (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) (Product_cat C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@id_func (Product_cat C C))
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod)) (@unit_adj_transf
  (Product_cat C C) C Prod (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t A T0))))
  (@one_cat_adjunction_family_transpose_agrees B (Product_cat C C) C (@one_cat_product_category C C C1 C1) C1 Prod
  (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t A T0) (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) X Y) Z h)) (@eq_trans _ _ _ _ (@eq_ap (Obj (Hom_cat (Functor_cat B (Product_cat C
  C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B (Product_cat C C)
  (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))) (@Transf B C X Z) (λ v : τ (Obj
  (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))),
  sigma_Fst (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) (@comp_cat_fapp0 B
  (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))
  (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z) (@fapp0 _ _ (@comp_cat_cov_fapp1_func B C
  (Product_cat C C) (@product_diagonal_func C) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor
  B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) h) v)) (@fapp0 (Hom_cat (Functor_cat (Product_cat C C)
  (Product_cat C C)) (@id_func (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) Prod)) (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) (Product_cat C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@id_func (Product_cat C C))
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) Prod)) (@unit_adj_transf
  (Product_cat C C) C Prod (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t A T0)))
  (@Struct_sigma (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (λ _ : τ (@Transf B C (@comp_cat_fapp0
  B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y))), (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C
  Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))) (@fapp0 (@Transf_cat (Product_cat
  C C) C (@Product_projL_func C C) Prod) (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y) (@Product_projL_func C C) Prod) (@one_cat_biproduct_inj1 C C1 Prod t A T0)) (@fapp0
  (@Transf_cat (Product_cat C C) C (@Product_projR_func C C) Prod) (@Transf_cat B C (@comp_cat_fapp0 B
  (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y) (@Product_projR_func C C) Prod) (@one_cat_biproduct_inj2 C C1 Prod t A T0)))
  (@one_cat_copair_unit_reindex_path B C C1 Prod t A T0 X Y)) (@eq_trans _ _ _ _ (@eq_ap (Obj (Hom_cat (Functor_cat
  B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat
  C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z))) (@Transf B C X Z) (λ v : τ (Obj
  (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 B (Product_cat C C) C
  Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z))),
  sigma_Fst (@comp_fapp0 (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) (@comp_cat_fapp0 B
  (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))
  (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z) v (@Struct_sigma (@Transf B C
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (λ _ : τ (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y))), (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)))) (@fapp0 (@Transf_cat (Product_cat C C) C (@Product_projL_func C
  C) Prod) (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B
  (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projL_func
  C C) Prod) (@one_cat_biproduct_inj1 C C1 Prod t A T0)) (@fapp0 (@Transf_cat (Product_cat C C) C
  (@Product_projR_func C C) Prod) (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C
  C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C)
  C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B
  (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projR_func
  C C) Prod) (@one_cat_biproduct_inj2 C C1 Prod t A T0))))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func B C (Product_cat
  C C) (@product_diagonal_func C) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) X Y)) Z) h) (@Struct_sigma (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C
  Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) (λ _ : τ (@Transf B C
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y)) Z), (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) Z)) h h) (@eq_ap (Functor (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C Prod
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) (Hom_cat (Functor_cat B (Product_cat
  C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z))) (Obj (Hom_cat (Functor_cat B
  (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat
  C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z))) (λ F : τ (Functor (@Transf_cat
  B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z) (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 B (Product_cat C C) C
  Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z))),
  @fapp0 (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z) (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C))
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y))) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)) F h) (@fapp1_func (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 B (Product_cat C C) C
  Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) (@product_diagonal_func
  (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X Y)) Z)) (@diagonal_family_action_path B C (@comp_cat_fapp0 B (Product_cat C C) C Prod
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z))) (@eq_trans _ _ _ _
  (@product_comp_first_path (Functor_cat B C) (Functor_cat B C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) (@comp_cat_fapp0 B
  (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))
  (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z) (@Struct_sigma (@Transf B C
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (λ _ : τ (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y))), (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)))) (@fapp0 (@Transf_cat (Product_cat C C) C (@Product_projL_func C
  C) Prod) (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B
  (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projL_func
  C C) Prod) (@one_cat_biproduct_inj1 C C1 Prod t A T0)) (@fapp0 (@Transf_cat (Product_cat C C) C
  (@Product_projR_func C C) Prod) (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C
  C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C)
  C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B
  (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projR_func
  C C) Prod) (@one_cat_biproduct_inj2 C C1 Prod t A T0))) (@Struct_sigma (@Transf B C (@comp_cat_fapp0 B
  (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) (λ _ : τ
  (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y)) Z), (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X Y)) Z)) h h)) (@eq_trans _ _ _ _ (@eq_refl (@Transf B C X Z) (@comp_fapp0
  (Functor_cat B C) X (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X Y)) Z h (@fapp0 (@Transf_cat (Product_cat C C) C (@Product_projL_func C C) Prod) (@Transf_cat
  B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _
  : τ (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projL_func C C) Prod) (@one_cat_biproduct_inj1 C C1 Prod
  t A T0)))) (@eq_ap (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y))) (@Transf B C X Z) (λ v : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y))), (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z h v)) (@fapp0 (@Transf_cat (Product_cat C C) C (@Product_projL_func C C) Prod) (@Transf_cat B C
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projL_func C C) Prod) (@one_cat_biproduct_inj1 C C1 Prod t A
  T0)) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X Y (@id (Functor_cat B
  C) X) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y))
  (@one_cat_biproduct_inj1_reindex_path B C C1 Prod t A T0 X Y)))))));

// The original mate inverse cut gives whole coproduct beta at the original first injection.
symbol one_cat_copair_first_injection_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (X Y : τ (Functor B C)) (Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z))
 : τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y)) Z (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f g) (@one_cat_product_family_pair B C C1
  Prod (@additive_binary_products C Prod t A) X X Y (@id (Functor_cat B C) X) (@zero_arrow_family_zero_transf B C
  t (@additive_terminal_object C Prod t A) T0 X Y))) f)
≔ (@eq_sym _ _ _ (@one_cat_uncopair_first_formula B C C1 Prod t A T0 X Y Z (@one_cat_copair_family B C C1 Prod t A
  T0 X Y Z f g)));
