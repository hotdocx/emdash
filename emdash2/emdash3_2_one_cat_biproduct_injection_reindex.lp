require open emdash.emdash3_2_one_cat_biproduct_family_reindex;
require open emdash.emdash3_2_product_family_reindex;

// The original identity-target restriction retains both native Hom actions.
symbol one_cat_biproduct_inj1_reindex_hom_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y : τ (Functor B C))
 : τ (@= (Functor (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C
  (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C)) (@id_func (Product_cat C C))) (Hom_cat
  (Functor_cat B (Product_cat C C)) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C)) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) (Product_cat C C) (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) (@Product_projL_func C C)) (@id_func (Product_cat C C))) (@Product_map_func
  (@Transf_cat (Product_cat C C) C (@Product_projL_func C C) (@Product_projL_func C C)) (@Transf_cat B C
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@Transf_cat (Product_cat C C) C (@Product_projL_func
  C C) (@Product_projR_func C C)) (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C
  C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C)
  C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))
  (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y) (@Product_projL_func C C) (@Product_projL_func C C)) (@comp_cat_con_fapp1_func B (Product_cat C C) C
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projL_func C C)
  (@Product_projR_func C C))))
≔ @eq_refl (Functor (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C)
  C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C)) (@id_func (Product_cat C C))) (Hom_cat
  (Functor_cat B (Product_cat C C)) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C)) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) (Product_cat C C) (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) (@Product_projL_func C C)) (@id_func (Product_cat C C)));

// Restrict the original injection input using whole identity and zero preservation.
symbol one_cat_biproduct_inj1_reindexed_input [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (X Y : τ (Functor B C))
 : τ (@= (@Transf B (Product_cat C C) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C)) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y)) (@fapp0 (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C)) (@id_func
  (Product_cat C C))) (Hom_cat (Functor_cat B (Product_cat C C)) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat
  C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C
  C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) X Y)) (@comp_cat_con_fapp1_func B (Product_cat C C) (Product_cat C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 (Product_cat C C) C
  (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C)) (@id_func (Product_cat C C)))
  (@Struct_sigma (@Transf (Product_cat C C) C (@Product_projL_func C C) (@Product_projL_func C C)) (λ _ : τ
  (@Transf (Product_cat C C) C (@Product_projL_func C C) (@Product_projL_func C C)), (@Transf (Product_cat C C) C
  (@Product_projL_func C C) (@Product_projR_func C C))) (@id (Functor_cat (Product_cat C C) C)
  (@Product_projL_func C C)) (@zero_arrow_family_zero_transf (Product_cat C C) C t (@additive_terminal_object C
  Prod t A) T0 (@Product_projL_func C C) (@Product_projR_func C C)))) (@Struct_sigma (@Transf B C (@comp_cat_fapp0
  B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (λ _ : τ (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))), (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))) (@id
  (Functor_cat B C) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) X Y))) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _
  : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))))
≔ @eq_trans _ _ _ _ (@eq_ap (Functor (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C)) (@id_func
  (Product_cat C C))) (Hom_cat (Functor_cat B (Product_cat C C)) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat
  C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C
  C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) X Y))) (@Transf B (Product_cat C C) (@comp_cat_fapp0 B (Product_cat C C)
  (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C)
  (@Product_projL_func C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (λ F : τ (Functor (Hom_cat (Functor_cat
  (Product_cat C C) (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) (@Product_projL_func C C)) (@id_func (Product_cat C C))) (Hom_cat (Functor_cat B
  (Product_cat C C)) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C
  (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C)) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))),
  @fapp0 (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C
  (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C)) (@id_func (Product_cat C C))) (Hom_cat
  (Functor_cat B (Product_cat C C)) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C)) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y)) F (@Struct_sigma (@Transf (Product_cat C C) C (@Product_projL_func C C) (@Product_projL_func
  C C)) (λ _ : τ (@Transf (Product_cat C C) C (@Product_projL_func C C) (@Product_projL_func C C)), (@Transf
  (Product_cat C C) C (@Product_projL_func C C) (@Product_projR_func C C))) (@id (Functor_cat (Product_cat C C) C)
  (@Product_projL_func C C)) (@zero_arrow_family_zero_transf (Product_cat C C) C t (@additive_terminal_object C
  Prod t A) T0 (@Product_projL_func C C) (@Product_projR_func C C)))) (@comp_cat_con_fapp1_func B (Product_cat C
  C) (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C)) (@id_func
  (Product_cat C C))) (@Product_map_func (@Transf_cat (Product_cat C C) C (@Product_projL_func C C)
  (@Product_projL_func C C)) (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@Transf_cat
  (Product_cat C C) C (@Product_projL_func C C) (@Product_projR_func C C)) (@Transf_cat B C (@comp_cat_fapp0 B
  (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projL_func C C) (@Product_projL_func C C))
  (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y) (@Product_projL_func C C) (@Product_projR_func C C))) (@one_cat_biproduct_inj1_reindex_hom_path B C C1
  Prod t A T0 X Y)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))) (@Transf B (Product_cat C C) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C)
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) (λ h : τ (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))), (@Struct_sigma (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))) (λ _ : τ (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))), (@Transf B C
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))) h (@fapp0 (@Transf_cat (Product_cat C C) C
  (@Product_projL_func C C) (@Product_projR_func C C)) (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y) (@Product_projL_func C C) (@Product_projR_func C C))
  (@zero_arrow_family_zero_transf (Product_cat C C) C t (@additive_terminal_object C Prod t A) T0
  (@Product_projL_func C C) (@Product_projR_func C C))))) (@fapp0 (@Transf_cat (Product_cat C C) C
  (@Product_projL_func C C) (@Product_projL_func C C)) (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y) (@Product_projL_func C C) (@Product_projL_func C C)) (@id (Functor_cat
  (Product_cat C C) C) (@Product_projL_func C C))) (@id (Functor_cat B C) (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))
  (@prewhisker_identity_path B (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y) (@Product_projL_func C C))) (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))) (@Transf B (Product_cat C C) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat C C)
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) (λ h : τ (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))), (@Struct_sigma (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))) (λ _ : τ (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))), (@Transf B C
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))) (@id (Functor_cat B C) (@comp_cat_fapp0 B
  (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X Y))) h)) (@fapp0 (@Transf_cat (Product_cat C C) C (@Product_projL_func C C) (@Product_projR_func C C))
  (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B
  (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projL_func
  C C) (@Product_projR_func C C)) (@zero_arrow_family_zero_transf (Product_cat C C) C t (@additive_terminal_object
  C Prod t A) T0 (@Product_projL_func C C) (@Product_projR_func C C))) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))
  (@one_cat_zero_family_prewhisker_path B (Product_cat C C) C C1 t (@additive_terminal_object C Prod t A) T0
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projL_func C C)
  (@Product_projR_func C C))));

// The original injection input retains its native Hom annotations.
symbol one_cat_biproduct_inj1_original_input [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (X Y : τ (Functor B C))
 : τ (Obj (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@fapp0 (Functor_cat (Product_cat C C) C)
  (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_cov_func (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C)) (@Product_projL_func C C)) (@id_func (Product_cat C C))))
≔ Struct_sigma (@id (Functor_cat (Product_cat C C) C) (@Product_projL_func C C)) (@zero_arrow_family_zero_transf
  (Product_cat C C) C t (@additive_terminal_object C Prod t A) T0 (@Product_projL_func C C) (@Product_projR_func C
  C));

// Compare the same two original input arrows before applying the native mate.
symbol one_cat_biproduct_inj1_original_input_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y : τ (Functor B C))
 : τ (@= (Obj (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@fapp0 (Functor_cat (Product_cat C C) C)
  (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_cov_func (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C)) (@Product_projL_func C C)) (@id_func (Product_cat C C))))
  (@one_cat_biproduct_inj1_original_input B C C1 Prod t A T0 X Y) (@Struct_sigma (@Transf (Product_cat C C) C
  (@Product_projL_func C C) (@Product_projL_func C C)) (λ _ : τ (@Transf (Product_cat C C) C (@Product_projL_func
  C C) (@Product_projL_func C C)), (@Transf (Product_cat C C) C (@Product_projL_func C C) (@Product_projR_func C
  C))) (@id (Functor_cat (Product_cat C C) C) (@Product_projL_func C C)) (@zero_arrow_family_zero_transf
  (Product_cat C C) C t (@additive_terminal_object C Prod t A) T0 (@Product_projL_func C C) (@Product_projR_func C
  C))))
≔ @eq_refl (Obj (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@fapp0 (Functor_cat (Product_cat C C)
  C) (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_cov_func (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C)) (@Product_projL_func C C)) (@id_func (Product_cat C C))))
  (@one_cat_biproduct_inj1_original_input B C C1 Prod t A T0 X Y);

// The original whole injection is the same native mate at the explicit whole input.
symbol one_cat_biproduct_inj1_original_formula [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y : τ (Functor B C))
 : τ (@= (@Transf (Product_cat C C) C (@Product_projL_func C C) Prod) (@one_cat_biproduct_inj1 C C1 Prod t A T0)
  (@fapp0 (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@fapp0 (Functor_cat (Product_cat C C) C)
  (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_cov_func (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C)) (@Product_projL_func C C)) (@id_func (Product_cat C C))) (Hom_cat (Functor_cat
  (Product_cat C C) C) (@Product_projL_func C C) (@fapp0 (Functor_cat (Product_cat C C) (Product_cat C C))
  (Functor_cat (Product_cat C C) C) (@comp_cat_cov_func (Product_cat C C) (Product_cat C C) C Prod) (@id_func
  (Product_cat C C)))) (@one_cat_adjunction_family_transpose_func (Product_cat C C) C (Product_cat C C) C1
  (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C C1
  Prod (@additive_binary_products C Prod t A)) (@Product_projL_func C C) (@id_func (Product_cat C C)))
  (@Struct_sigma (@Transf (Product_cat C C) C (@Product_projL_func C C) (@Product_projL_func C C)) (λ _ : τ
  (@Transf (Product_cat C C) C (@Product_projL_func C C) (@Product_projL_func C C)), (@Transf (Product_cat C C) C
  (@Product_projL_func C C) (@Product_projR_func C C))) (@id (Functor_cat (Product_cat C C) C)
  (@Product_projL_func C C)) (@zero_arrow_family_zero_transf (Product_cat C C) C t (@additive_terminal_object C
  Prod t A) T0 (@Product_projL_func C C) (@Product_projR_func C C)))))
≔ (@eq_ap (Obj (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@fapp0 (Functor_cat (Product_cat C C)
  C) (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_cov_func (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C)) (@Product_projL_func C C)) (@id_func (Product_cat C C)))) (@Transf (Product_cat C C)
  C (@Product_projL_func C C) Prod) (λ h : τ (Obj (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C))
  (@fapp0 (Functor_cat (Product_cat C C) C) (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_cov_func
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C)) (@Product_projL_func C C)) (@id_func
  (Product_cat C C)))), @fapp0 (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C)) (@fapp0 (Functor_cat
  (Product_cat C C) C) (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_cov_func (Product_cat C C) C
  (Product_cat C C) (@product_diagonal_func C)) (@Product_projL_func C C)) (@id_func (Product_cat C C))) (Hom_cat
  (Functor_cat (Product_cat C C) C) (@Product_projL_func C C) (@fapp0 (Functor_cat (Product_cat C C) (Product_cat
  C C)) (Functor_cat (Product_cat C C) C) (@comp_cat_cov_func (Product_cat C C) (Product_cat C C) C Prod)
  (@id_func (Product_cat C C)))) (@one_cat_adjunction_family_transpose_func (Product_cat C C) C (Product_cat C C)
  C1 (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C
  C1 Prod (@additive_binary_products C Prod t A)) (@Product_projL_func C C) (@id_func (Product_cat C C))) h)
  (@one_cat_biproduct_inj1_original_input B C C1 Prod t A T0 X Y) (@Struct_sigma (@Transf (Product_cat C C) C
  (@Product_projL_func C C) (@Product_projL_func C C)) (λ _ : τ (@Transf (Product_cat C C) C (@Product_projL_func
  C C) (@Product_projL_func C C)), (@Transf (Product_cat C C) C (@Product_projL_func C C) (@Product_projR_func C
  C))) (@id (Functor_cat (Product_cat C C) C) (@Product_projL_func C C)) (@zero_arrow_family_zero_transf
  (Product_cat C C) C t (@additive_terminal_object C Prod t A) T0 (@Product_projL_func C C) (@Product_projR_func C
  C))) (@one_cat_biproduct_inj1_original_input_path B C C1 Prod t A T0 X Y));

// Whole terminal/initial uniqueness compares the same local zero before the native mate.
symbol one_cat_biproduct_inj1_local_input_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y : τ (Functor B C))
 : τ (@= (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) X Y))) (@Struct_sigma (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))) (λ _ : τ (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))), (@Transf B C
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))) (@id (Functor_cat B C) (@comp_cat_fapp0 B
  (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X Y))) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@comp_cat_fapp0 B
  (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)))) (@Struct_sigma (@Transf B C X X) (λ _ : τ (@Transf B C X X), (@Transf B C X
  Y)) (@id (Functor_cat B C) X) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X
  Y)))
≔ (@eq_ap (@Transf B C X Y) (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat
  B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (λ h : τ (@Transf B C X Y), (@Struct_sigma (@Transf B
  C X X) (λ _ : τ (@Transf B C X X), (@Transf B C X Y)) (@id (Functor_cat B C) X) h))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@comp_cat_fapp0 B (Product_cat
  C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y)
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@Const_func B C t) Y) (@Transf B C X Y) (λ h : τ (@Transf B C
  (@Const_func B C t) Y), (@comp_fapp0 (Functor_cat B C) X (@Const_func B C t) Y h (@diagram_family_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@one_cat_initial_family_arrow_path B C C1 t T0 Y
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))) (@eq_ap (@Transf B C X (@Const_func B C t)) (@Transf B C X Y) (λ h : τ (@Transf B C X
  (@Const_func B C t)), (@comp_fapp0 (Functor_cat B C) X (@Const_func B C t) Y (@diagram_family_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y)
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) h)) (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) X)
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_terminal_family_arrow_path B C C1 t
  (@additive_terminal_object C Prod t A) X (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))) walking_arrow_src walking_arrow_tgt walking_arrow_generator)))));

// The original whole injection restricts to the original native product pair.
symbol one_cat_biproduct_inj1_reindex_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (X Y : τ (Functor B C))
 : τ (@= (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@fapp0
  (@Transf_cat (Product_cat C C) C (@Product_projL_func C C) Prod) (@Transf_cat B C X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@Product_projL_func C C) Prod) (@one_cat_biproduct_inj1
  C C1 Prod t A T0)) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X Y (@id
  (Functor_cat B C) X) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y)))
≔ @eq_trans _ _ _ _ (@eq_ap (@Transf (Product_cat C C) C (@Product_projL_func C C) Prod) (@Transf B C X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (λ h : τ (@Transf (Product_cat C C) C
  (@Product_projL_func C C) Prod), @fapp0 (@Transf_cat (Product_cat C C) C (@Product_projL_func C C) Prod)
  (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))
  (@comp_cat_con_fapp1_func B (Product_cat C C) C (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y) (@Product_projL_func C C) Prod) h) (@one_cat_biproduct_inj1 C C1 Prod t A T0) (@fapp0 (Hom_cat
  (Functor_cat (Product_cat C C) (Product_cat C C)) (@fapp0 (Functor_cat (Product_cat C C) C) (Functor_cat
  (Product_cat C C) (Product_cat C C)) (@comp_cat_cov_func (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C)) (@Product_projL_func C C)) (@id_func (Product_cat C C))) (Hom_cat (Functor_cat
  (Product_cat C C) C) (@Product_projL_func C C) (@fapp0 (Functor_cat (Product_cat C C) (Product_cat C C))
  (Functor_cat (Product_cat C C) C) (@comp_cat_cov_func (Product_cat C C) (Product_cat C C) C Prod) (@id_func
  (Product_cat C C)))) (@one_cat_adjunction_family_transpose_func (Product_cat C C) C (Product_cat C C) C1
  (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C C1
  Prod (@additive_binary_products C Prod t A)) (@Product_projL_func C C) (@id_func (Product_cat C C)))
  (@Struct_sigma (@Transf (Product_cat C C) C (@Product_projL_func C C) (@Product_projL_func C C)) (λ _ : τ
  (@Transf (Product_cat C C) C (@Product_projL_func C C) (@Product_projL_func C C)), (@Transf (Product_cat C C) C
  (@Product_projL_func C C) (@Product_projR_func C C))) (@id (Functor_cat (Product_cat C C) C)
  (@Product_projL_func C C)) (@zero_arrow_family_zero_transf (Product_cat C C) C t (@additive_terminal_object C
  Prod t A) T0 (@Product_projL_func C C) (@Product_projR_func C C)))) (@one_cat_biproduct_inj1_original_formula B C
  C1 Prod t A T0 X Y)) (@eq_trans _ _ _ _ (@one_cat_transpose_reindex_path B (Product_cat C C) C (Product_cat C C)
  C1 (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C
  C1 Prod (@additive_binary_products C Prod t A)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y) (@Product_projL_func C C) (@id_func (Product_cat C C)) (@Struct_sigma (@Transf (Product_cat C C) C
  (@Product_projL_func C C) (@Product_projL_func C C)) (λ _ : τ (@Transf (Product_cat C C) C (@Product_projL_func
  C C) (@Product_projL_func C C)), (@Transf (Product_cat C C) C (@Product_projL_func C C) (@Product_projR_func C
  C))) (@id (Functor_cat (Product_cat C C) C) (@Product_projL_func C C)) (@zero_arrow_family_zero_transf
  (Product_cat C C) C t (@additive_terminal_object C Prod t A) T0 (@Product_projL_func C C) (@Product_projR_func C
  C)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B (Product_cat C C) (@comp_cat_fapp0 B (Product_cat C C) (Product_cat
  C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C
  C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) X Y)) (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C
  C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (λ h : τ (@Transf B (Product_cat C C) (@comp_cat_fapp0 B (Product_cat C C)
  (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C)
  (@Product_projL_func C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)), (@fapp0 (Hom_cat (Functor_cat B
  (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) (@Transf_cat B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C
  C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (@one_cat_adjunction_family_transpose_func B C (Product_cat C C) C1
  (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C C1
  Prod (@additive_binary_products C Prod t A)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) h)) (@fapp0 (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C))
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C))
  (@id_func (Product_cat C C))) (Hom_cat (Functor_cat B (Product_cat C C)) (@comp_cat_fapp0 B (Product_cat C C)
  (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C)
  (@Product_projL_func C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_con_fapp1_func B (Product_cat
  C C) (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) (@Product_projL_func C C)) (@id_func
  (Product_cat C C))) (@Struct_sigma (@Transf (Product_cat C C) C (@Product_projL_func C C) (@Product_projL_func C
  C)) (λ _ : τ (@Transf (Product_cat C C) C (@Product_projL_func C C) (@Product_projL_func C C)), (@Transf
  (Product_cat C C) C (@Product_projL_func C C) (@Product_projR_func C C))) (@id (Functor_cat (Product_cat C C) C)
  (@Product_projL_func C C)) (@zero_arrow_family_zero_transf (Product_cat C C) C t (@additive_terminal_object C
  Prod t A) T0 (@Product_projL_func C C) (@Product_projR_func C C)))) (@Struct_sigma (@Transf B C (@comp_cat_fapp0
  B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))) (λ _ : τ (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))), (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))) (@id
  (Functor_cat B C) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) X Y))) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _
  : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))) (@one_cat_biproduct_inj1_reindexed_input
  B C C1 Prod t A T0 X Y)) (@eq_trans _ _ _ _ (@eq_refl (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y))) (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@Transf_cat B C X (@fapp0 (Functor_cat
  B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@one_cat_adjunction_family_transpose_func B C (Product_cat C C)
  C1 (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C
  C1 Prod (@additive_binary_products C Prod t A)) X (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) (@Struct_sigma (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (λ _ : τ
  (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _
  : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))), (@Transf B C (@comp_cat_fapp0 B
  (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)))) (@id (Functor_cat B C) (@comp_cat_fapp0 B (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@comp_cat_fapp0 B (Product_cat
  C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)))))) (@eq_ap (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (@Transf B C X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y))) (λ h : τ (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))), @fapp0
  (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y))) (@one_cat_adjunction_family_transpose_func B C (Product_cat C C) C1 (@one_cat_product_category C C C1
  C1) (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C C1 Prod (@additive_binary_products C
  Prod t A)) X (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) h) (@Struct_sigma (@Transf
  B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))) (λ _ : τ (@Transf B C (@comp_cat_fapp0
  B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y))), (@Transf B C (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C
  C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C)
  C (@Product_projR_func C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))) (@id
  (Functor_cat B C) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) X Y))) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projL_func C C) (@Struct_sigma (Functor B C) (λ _
  : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C (@Product_projR_func C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)))) (@Struct_sigma (@Transf B C X X) (λ _
  : τ (@Transf B C X X), (@Transf B C X Y)) (@id (Functor_cat B C) X) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y)) (@one_cat_biproduct_inj1_local_input_path B C C1 Prod t A T0 X
  Y)))));
