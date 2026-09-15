/* Original Q(a) and upper-right differential quotient comparison. */
require open emdash.emdash3_2_one_cat_copair_annihilation_views;
require open emdash.emdash3_2_one_cat_short_exact_family_colifts;
require open emdash.emdash3_2_one_cat_native_window_snake_inputs;
require open emdash.emdash3_2_one_cat_zero_cone_column_inputs;
require open emdash.emdash3_2_one_cat_cokernel_family_annihilation;

// The original Q(a) unit annihilates [bₘ,i₀] via the original input recovery path.
symbol one_cat_native_window_snake_right_incoming_quotient_copair_zero [K C : Cat] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@= (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
  (@comp_fapp0 (Functor_cat K C) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_incoming K C C1 Prod t Add T0 Rm R0 mm)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src))
  (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))) (λ v
  : τ (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)),
  (@comp_fapp0 (Functor_cat K C) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) v)) _
  _ (@eq_sym _ _ _ (@one_cat_native_window_snake_input_incoming_path K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero))) (@one_cat_cokernel_family_annihilation_path K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@native_snake_incoming_diagram K C t
  (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero))));

// Whole uncopairing extracts annihilation of the original row inclusion.
symbol one_cat_native_window_snake_right_row_zero [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@= (@Transf K C (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R0) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R0))
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))))
≔ (@one_cat_copair_postcompose_second_zero_path K C C1 Prod t Add T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) Rm
  R0 mm walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod
  t Add) R0) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_incoming_quotient_copair_zero K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0));

// Whole uncopairing extracts annihilation of the original previous middle map.
symbol one_cat_native_window_snake_right_previous_middle_zero [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero)
  C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R0 walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) Rm R0 mm
  walking_arrow_src)) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))))
≔ (@one_cat_copair_postcompose_first_zero_path K C C1 Prod t Add T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) Rm
  R0 mm walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod
  t Add) R0) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_incoming_quotient_copair_zero K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0));

// The row square and original Q(dₘᴰ) unit make q_d∘p₀ kill the recovered incoming a.
symbol one_cat_native_window_snake_right_quotient_forward_zero [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero)
  C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@= (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm)))
  (@comp_fapp0 (Functor_cat K C) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0)) (@native_snake_incoming
  K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero))) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@cokernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add)
  Rm R0 mm))))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src))
  (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))) (λ v : τ
  (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)),
  (@comp_fapp0 (Functor_cat K C) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0)) v)) _ _
  (@one_cat_native_window_snake_input_incoming_path K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero)) (@one_cat_copair_postcompose_zero_path K C C1 Prod t Add T0 (@zero_cone_row_family_vertex_func
  K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C
  t (@additive_terminal_object C Prod t Add) R0) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src) (@one_cat_zero_cone_row_family_incoming
  K C C1 t (@additive_terminal_object C Prod t Add) R0) (@comp_fapp0 (Functor_cat K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0)) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K
  C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt))
  (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))) (λ v : τ
  (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_tgt)), (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) v)) _ _ (@eq_sym _ _ _
  (@one_cat_zero_cone_row_outgoing_square_path K C C1 t (@additive_terminal_object C Prod t Add) Rm R0 mm)))
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_tgt) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_tgt) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) Rm)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_tgt)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))) (@Transf K
  C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))) (λ v : τ
  (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))),
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  Rm walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm)) v
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) Rm))) _ _
  (@one_cat_cokernel_family_annihilation_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm))) (@one_cat_zero_family_precompose_path K C C1 t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_tgt) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) Rm)))))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat K C) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0)
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R0))) (@eq_trans _
  _ _ _ (@eq_ap (@Transf K C (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt))
  (@Transf K C (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))) (λ v : τ
  (@Transf K C (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt)),
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R0) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm)) v)) _ _
  (@one_cat_zero_family_chain_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_row_family_diagram_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@one_cat_zero_cone_row_family_transf K C C1 t (@additive_terminal_object C Prod t Add) R0)))
  (@one_cat_zero_family_postcompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm)))))));

// φ:Q(a)⇒Q(dₘᴰ) is the original whole quotient descent of q_d∘p₀.
symbol one_cat_native_window_snake_right_quotient_forward [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@Transf K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm)))
≔ (@one_cat_cokernel_family_descent K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0
  (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_window_snake_right_quotient_forward_zero K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0));

// The original quotient reconstructs φ∘π_a=q_d∘p₀.
symbol one_cat_native_window_snake_right_quotient_forward_reconstruction [K C : Cat] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm)))
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C
  Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0
  (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0)))
≔ (@one_cat_cokernel_family_descent_ambient_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@native_snake_incoming_diagram K C t
  (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_window_snake_right_quotient_forward_zero K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0));

// The original short-exact row colifts π_a along p₀, without a section into B₀.
symbol one_cat_native_window_snake_right_row_colift [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
≔ (@one_cat_short_exact_family_colift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C
  Prod t Add) T0 P Q (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_row_family_diagram_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@one_cat_zero_cone_row_family_transf K C C1 t (@additive_terminal_object C Prod t Add) R0) E0
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_row_zero K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0));

// The whole row colift reconstructs x∘p₀=π_a.
symbol one_cat_native_window_snake_right_row_colift_reconstruction [K C : Cat] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_row_colift K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
≔ (@one_cat_short_exact_family_colift_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0) (@zero_cone_row_family_diagram_func K C t
  (@additive_terminal_object C Prod t Add) R0) (@one_cat_zero_cone_row_family_transf K C C1 t
  (@additive_terminal_object C Prod t Add) R0) E0 (@cokernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0
  (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_row_zero K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0));

// The original previous-row quotient cancels to give x∘dₘᴰ=0.
symbol one_cat_native_window_snake_right_quotient_backward_zero [K C : Cat] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_tgt) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_row_colift K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) Rm R0 mm
  walking_arrow_tgt)) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_tgt)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))))
≔ (@one_cat_short_exact_family_outgoing_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) Rm) (@zero_cone_row_family_diagram_func K C t
  (@additive_terminal_object C Prod t Add) Rm) (@one_cat_zero_cone_row_family_transf K C C1 t
  (@additive_terminal_object C Prod t Add) Rm) Em (@cokernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0
  (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_tgt) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_row_colift K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) Rm R0 mm
  walking_arrow_tgt)) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_tgt)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
  (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_tgt) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero))) (@one_cat_native_window_snake_right_row_colift K C C1 Prod t Add T0 P Q Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C
  Prod t Add) Rm R0 mm walking_arrow_tgt) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C
  Prod t Add) Rm))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt)) (@Transf K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))) (λ v
  : τ (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_tgt)), (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero))) (@one_cat_native_window_snake_right_row_colift K C C1 Prod t Add T0 P Q Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0) v)) _ _ (@one_cat_zero_cone_row_outgoing_square_path K C C1 t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_row_colift K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) Rm R0 mm
  walking_arrow_src)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero)))) (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C
  Prod t Add) Rm walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))) (λ v
  : τ (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))),
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R0 walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) v
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) Rm R0 mm
  walking_arrow_src))) _ _ (@one_cat_native_window_snake_right_row_colift_reconstruction K C C1 Prod t Add T0
  P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) (@eq_trans _ _ _ _
  (@one_cat_native_window_snake_right_previous_middle_zero K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@eq_sym _ _ _ (@one_cat_zero_family_precompose_path K C C1 t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_tgt) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero))) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add)
  Rm)))))))));

// ψ:Q(dₘᴰ)⇒Q(a) descends the original row colift x.
symbol one_cat_native_window_snake_right_quotient_backward [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@Transf K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
≔ (@one_cat_cokernel_family_descent K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 Q (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0
  mm) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_row_colift K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_backward_zero K C C1 Prod t Add T0 P Q Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0));

// The original quotient reconstructs ψ∘q_d=x.
symbol one_cat_native_window_snake_right_quotient_backward_reconstruction [K C : Cat] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_quotient_backward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C
  Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm
  R0 mm))) (@one_cat_native_window_snake_right_row_colift K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0))
≔ (@one_cat_cokernel_family_descent_ambient_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero))) (@one_cat_native_window_snake_right_row_colift K C C1 Prod t Add T0 P Q Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_backward_zero K C C1 Prod
  t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0));

// The original Q(a) quotient cancels to prove ψ∘φ=id.
symbol one_cat_native_window_snake_right_quotient_backward_forward [K C : Cat] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@= (@Transf K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
  (@comp_fapp0 (Functor_cat K C) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_quotient_backward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) (@id (Functor_cat K C) (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t
  (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero)))))
≔ (@one_cat_cokernel_family_quotient_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@native_snake_incoming_diagram K C t
  (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@comp_fapp0 (Functor_cat K C) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_quotient_backward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) (@id (Functor_cat K C) (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t
  (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero)))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_quotient_backward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero))))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm))) (@Transf K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero)))) (λ v : τ (@Transf K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm))), (@comp_fapp0 (Functor_cat K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_quotient_backward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) v)) _ _ (@one_cat_native_window_snake_right_quotient_forward_reconstruction K C
  C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_snake_right_quotient_backward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C
  Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm
  R0 mm)) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0)) (@eq_trans _ _ _
  _ (@eq_ap (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
  (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))) (λ v
  : τ (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))),
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) v
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))) _ _
  (@one_cat_native_window_snake_right_quotient_backward_reconstruction K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm
  m0 m1 upper_zero lower_zero Em E0)) (@one_cat_native_window_snake_right_row_colift_reconstruction K C C1
  Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0))))));

// Original p₀ and Q(dₘᴰ) cancellation prove φ∘ψ=id.
symbol one_cat_native_window_snake_right_quotient_forward_backward [K C : Cat] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@= (@Transf K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm)))
  (@comp_fapp0 (Functor_cat K C) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_backward K C C1 Prod t Add T0 P Q
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) (@id (Functor_cat K C) (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm))))
≔ (@one_cat_cokernel_family_quotient_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@comp_fapp0 (Functor_cat K C)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_backward K C C1 Prod t Add T0 P Q
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) (@id (Functor_cat K C) (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_backward K C C1 Prod t Add T0 P Q
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
  (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))) (λ v : τ
  (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))),
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) v)) _ _ (@one_cat_native_window_snake_right_quotient_backward_reconstruction K
  C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0))
  (@one_cat_short_exact_family_outgoing_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0) (@zero_cone_row_family_diagram_func K C t
  (@additive_terminal_object C Prod t Add) R0) (@one_cat_zero_cone_row_family_transf K C C1 t
  (@additive_terminal_object C Prod t Add) R0) E0 (@cokernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add)
  Rm R0 mm)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_row_colift K C C1 Prod t Add T0 P Q Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_row_colift K C C1 Prod t Add T0 P Q Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object
  C Prod t Add) R0))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero)))) (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C
  Prod t Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))) (λ
  v : τ (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))),
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) v)) _ _ (@one_cat_native_window_snake_right_row_colift_reconstruction K C C1
  Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0))
  (@one_cat_native_window_snake_right_quotient_forward_reconstruction K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm
  m0 m1 upper_zero lower_zero Em E0)))))));

// Fixed-forward ΩAlong(φ) retains the recovered incoming diagram and both original Q choices.
symbol one_cat_native_window_snake_right_quotient_equiv [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm))
  (E0 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0))
  : τ (@OmegaEquivAlong (Functor_cat K C) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0
  (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0))
≔ (@omega_equiv_along_intro (Functor_cat K C) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0
  (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_backward K C C1 Prod t Add T0 P Q
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_backward K C
  C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)
  (@one_cat_native_window_snake_right_quotient_backward_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_forward_backward K C C1 Prod t Add
  T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0));
