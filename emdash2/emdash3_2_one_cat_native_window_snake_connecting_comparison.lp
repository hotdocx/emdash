/* Whole native snake and LES connecting comparison at the original H endpoints. */
require open emdash.emdash3_2_one_cat_native_window_snake_connecting_covers;
require open emdash.emdash3_2_one_cat_native_window_snake_left_homology;

// Original row and cycle inclusions identify the two covered left-cycle maps.
symbol one_cat_native_window_snake_connecting_cover_left_cycles_comparison [K C : Cat] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
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
  (E1 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R1))
  (E2 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R2))
  : τ (@= (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1))) (@comp_fapp0 (Functor_cat K C)
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2) (@comp_fapp0
  (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_snake_cover_source K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_snake_covered_lift
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0
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
  (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@one_cat_native_cover_left_cycles K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@kernel_precomposition_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1) (@comp_fapp0 (Functor_cat K C)
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2) (@comp_fapp0
  (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_snake_cover_source K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_snake_covered_lift
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0
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
  (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@one_cat_native_cover_left_cycles K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)
  (@one_cat_short_exact_family_incoming_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_diagram_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@one_cat_zero_cone_row_family_transf K C C1 t
  (@additive_terminal_object C Prod t Add) R1) E1 (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0)) (@comp_fapp0
  (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@comp_fapp0
  (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@one_cat_native_window_snake_cycles_backward K C C1
  Prod t Add T0 P Q R1 R2 m1 E1 E2) (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1
  t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K
  C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C),
  Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero)) (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))) (@comp_fapp0 (Functor_cat K C)
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@one_cat_native_cover_left_cycles K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q R0 R1 R2 m0 m1
  lower_zero E1 E2)) (@eq_trans _ _ _ _ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)) (@Transf K C
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (λ
  v : τ (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1)), (@comp_fapp0 (Functor_cat K C)
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R1) v)) _ _
  (@comp_assoc (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2) (@comp_fapp0
  (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_snake_cover_source K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_snake_covered_lift
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0
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
  (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)) (@Transf K C
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (λ
  v : τ (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1)), (@comp_fapp0 (Functor_cat K C)
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R1) v)) _ _
  (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R1)) (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1)) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R1)), (@comp_fapp0 (Functor_cat K C)
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R1) v (@comp_fapp0 (Functor_cat K C)
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1
  t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K
  C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C),
  Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero)) (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))) _ _
  (@one_cat_native_window_snake_cycles_backward_reconstruction K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)))
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C
  C1 t (@additive_terminal_object C Prod t Add) R1) (@one_cat_native_window_snake_cycles_row_lift K C C1 Prod
  t Add T0 P Q R1 R2 m1 E1) (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1
  t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K
  C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C),
  Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero)) (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (@Transf K C
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (λ
  v : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) v (@comp_fapp0 (Functor_cat K C)
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1
  t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K
  C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C),
  Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero)) (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))) _ _
  (@one_cat_native_window_snake_cycles_row_reconstruction K C C1 Prod t Add T0 P Q R1 R2 m1 E1)) (@eq_trans _
  _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_snake_cover_source K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1
  t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K
  C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C),
  Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero)) (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src)) (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (λ v : τ (@Transf K C
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src)), (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) v (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) _ _ (@one_cat_native_snake_covered_lift_reconstruction K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0
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
  (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0
  walking_arrow_src) (@one_cat_native_snake_cover_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)) (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_ap (@Transf K C (@kernel_precomposition_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src))
  (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (λ v : τ (@Transf K C
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)),
  (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) v)) _ _
  (@one_cat_native_window_snake_connecting_cover_map_reconstruction K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm
  m0 m1 upper_zero lower_zero Em E0 E1 E2))))))))) (@eq_sym _ _ _ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)) (@Transf K C
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (λ
  v : τ (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1)), (@comp_fapp0 (Functor_cat K C)
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R1) v)) _ _
  (@one_cat_native_cover_cycles_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2))
  (@one_cat_native_cover_left_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R0 R1 m0 E1))))));

// The actual left-H comparison identifies the two original covered connecting formulas.
symbol one_cat_native_window_snake_connecting_covered_comparison [K C : Cat] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
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
  (E1 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R1))
  (E2 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R2))
  : τ (@= (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_window_target_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero E1 E2) (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_snake_covered_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)) (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@one_cat_native_window_covered_transf K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))) (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_window_target_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2)) (λ v : τ (@Transf K C (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))), (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero E1 E2) v)) _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0
  Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)) (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero E1 E2) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1
  t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K
  C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C),
  Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_outgoing
  K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero)) (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_window_target_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2)) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)),
  (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) v (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_snake_cover_source K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_snake_covered_lift
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0
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
  (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)))) _ _ (@one_cat_native_window_snake_left_forward_reconstruction K C C1
  Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero E1 E2)) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@comp_assoc (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@one_cat_native_window_target_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2) (@homology_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)
  (@one_cat_native_window_left_column_input K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2) (@comp_fapp0
  (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_snake_cover_source K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_snake_covered_lift
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0
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
  (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)))) (@eq_ap (@Transf K C (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)))
  (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_window_target_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2)) (λ v : τ (@Transf K C (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))),
  (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@one_cat_native_window_target_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2) (@homology_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)
  (@one_cat_native_window_left_column_input K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) v))
  _ _ (@one_cat_native_window_snake_connecting_cover_left_cycles_comparison K C C1 Prod t Add T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))))));

// Original whole LES-cover uniqueness proves L∘∂∘R⁻¹=δ with the positive sign.
symbol one_cat_native_window_snake_connecting_agrees [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
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
  (E1 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R1))
  (E2 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R2))
  : τ (@= (@Transf K C (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add)
  C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_window_source_homology_func K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero E1 E2) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_window_source_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N (@fapp0
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
  (@omega_equiv_along_left_inv (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_snake_right_homology_comparison K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_snake_right_homology_equiv K C C1 Prod t Add T0 P
  Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))) (@one_cat_native_window_connecting_transf K C
  C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
≔ (@one_cat_native_window_connecting_unique K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2 (@comp_fapp0 (Functor_cat K C) (@one_cat_native_window_source_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero E1 E2) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_window_source_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N (@fapp0
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
  (@omega_equiv_along_left_inv (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_snake_right_homology_comparison K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_snake_right_homology_equiv K C C1 Prod t Add T0 P
  Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@comp_assoc (Functor_cat K C) (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_window_source_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero E1 E2) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_window_source_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N (@fapp0
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
  (@omega_equiv_along_left_inv (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_snake_right_homology_comparison K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_snake_right_homology_equiv K C C1 Prod t Add T0 P
  Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@one_cat_native_window_cover_transf K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))) (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_window_target_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2)) (λ v : τ (@Transf K C (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))), (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero E1 E2) v)) _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N (@fapp0
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
  (@omega_equiv_along_left_inv (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_snake_right_homology_comparison K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_snake_right_homology_equiv K C C1 Prod t Add T0 P
  Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_cover_transf K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))) (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_window_target_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2)) (λ v : τ (@Transf K C (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))), (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero E1 E2) v)) _ _ (@eq_ap (@Transf K C (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))) (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))) (λ v : τ (@Transf K C (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))), (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N (@fapp0
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)) v)) _
  _ (@one_cat_native_window_snake_connecting_cover_homology_comparison K C C1 Prod t Add T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))) (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_window_target_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2)) (λ v : τ (@Transf K C (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))), (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero E1 E2) v)) _ _ (@comp_assoc (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) (@one_cat_native_snake_connecting_transf K
  C C1 Prod t Add T0 P Q N (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@one_cat_native_snake_cover_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)) (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_precomposition_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0
  R1 m0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))) (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@one_cat_native_window_target_homology_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2)) (λ v : τ (@Transf K C (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))), (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero E1 E2) v)) _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_cover_source K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0
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
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))) (@Transf K C (@kernel_precomposition_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))) (λ v : τ (@Transf K C (@one_cat_native_snake_cover_source K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@fapp0
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
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))), (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0))
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) v (@one_cat_native_window_snake_connecting_cover_map K C C1 Prod t Add T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) _ _ (@one_cat_native_snake_connecting_reconstruction
  K C C1 Prod t Add T0 P Q N (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)))) (@one_cat_native_window_snake_connecting_covered_comparison K C C1 Prod t Add T0 P
  Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))))));

// The same original connecting comparison gives the whole equation L∘∂=δ∘R.
symbol one_cat_native_window_snake_connecting_forward_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
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
  (E1 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R1))
  (E2 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R2))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero E1 E2) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N (@fapp0 (Functor_cat K
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
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_connecting_transf K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_snake_right_homology_comparison K C C1 Prod t Add T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))) (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (λ
  v : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero)))), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero E1 E2) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N (@fapp0 (Functor_cat K
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
  _ (@eq_sym _ _ _ (@omega_equiv_along_left_law (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@one_cat_native_window_snake_right_homology_comparison K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_snake_right_homology_equiv K C C1 Prod t Add
  T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))) (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero E1 E2) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N (@fapp0
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
  (@omega_equiv_along_left_inv (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_snake_right_homology_comparison K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_snake_right_homology_equiv K C C1 Prod t Add T0 P
  Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_native_window_snake_right_homology_comparison K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (λ
  v : τ (@Transf K C (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1
  t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) v
  (@one_cat_native_window_snake_right_homology_comparison K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@one_cat_native_window_snake_left_homology_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero E1 E2) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N (@fapp0
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
  (@omega_equiv_along_left_inv (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_snake_right_homology_comparison K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_snake_right_homology_equiv K C C1 Prod t Add T0 P
  Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))))) (@eq_ap (@Transf K C
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (λ
  v : τ (@Transf K C (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1
  t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) v
  (@one_cat_native_window_snake_right_homology_comparison K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) _ _ (@one_cat_native_window_snake_connecting_agrees K C C1 Prod t Add
  T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))));

// The derived whole equation supplies a native connecting-diagram map with endpoint actions R and L.
symbol one_cat_native_window_snake_connecting_diagram_map [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
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
  (E1 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R1))
  (E2 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R2))
  : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N (@fapp0
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
  (@transf_arrow_diagram_func K C (@one_cat_native_window_source_homology_func K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_connecting_transf K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2)))
≔ (@one_cat_square_family_transf K C C1 (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
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
  (@one_cat_native_window_source_homology_func K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
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
  upper_zero lower_zero))) (@one_cat_native_window_target_homology_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N (@fapp0 (Functor_cat K
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))
  (@one_cat_native_window_connecting_transf K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_snake_right_homology_comparison K C C1 Prod t Add T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_snake_left_homology_forward
  K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero E1 E2)
  (@one_cat_native_window_snake_connecting_forward_path K C C1 Prod t Add T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2));
