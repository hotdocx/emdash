/* Whole comparison of the original left cycles with the original K(c).
   All action is retained by existing row and kernel mate functors. */
require open emdash.emdash3_2_one_cat_native_window_snake_inputs;
require open emdash.emdash3_2_one_cat_zero_cone_column_inputs;
require open emdash.emdash3_2_one_cat_short_exact_family_lifts;
require open emdash.emdash3_2_one_cat_product_family_projection_paths;

// The original row inclusion sends left cycles into K(c), by the derived whole row square.
symbol one_cat_native_window_snake_cycles_forward_zero [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K
  C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C),
  Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_tgt)))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R1)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)))) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K
  C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C),
  Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_tgt)))))
≔ (@one_cat_product_pair_precompose_zero_path K C C1 Prod t Add T0 (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C
  C1 t (@additive_terminal_object C Prod t Add) R1) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R1) (@eq_trans _ _ _ _
  (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming
  K C C1 t (@additive_terminal_object C Prod t Add) R1) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))) (@eq_trans
  _ _ _ _ (@eq_ap (@Transf K C (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R1) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2
  walking_arrow_src)) (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)) (λ v : τ (@Transf K C
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) v (@kernel_adjunction_family_inclusion_transf
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)))) _ _
  (@one_cat_zero_cone_row_incoming_square_path K C C1 t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R2)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R2)
  (@zero_cone_row_family_source_map K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R2)) (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)) (λ
  v : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R2)), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R2)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R2) v)) _ _
  (@one_cat_kernel_family_annihilation_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1))) (@one_cat_zero_family_postcompose_path K C C1 t
  (@additive_terminal_object C Prod t Add) T0 (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R2) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C
  C1 t (@additive_terminal_object C Prod t Add) R2)))))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R1)
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R1)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))
  (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)) (λ v : τ (@Transf K C
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt) v (@kernel_adjunction_family_inclusion_transf
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)))) _ _
  (@one_cat_zero_family_chain_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_diagram_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@one_cat_zero_cone_row_family_transf K C C1 t (@additive_terminal_object C Prod t Add) R1)))
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1))))));

// u:Z(A₁)⇒K(c) is the original whole kernel mate; no row exactness is needed.
symbol one_cat_native_window_snake_cycles_forward [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))))
≔ (@one_cat_kernel_family_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod
  t
  Add) T0 P (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1)) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R1)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1))) (@one_cat_native_window_snake_cycles_forward_zero K C
  C1 Prod t Add T0 P R1 R2 m1));

// The original kernel inclusion reconstructs κ_c∘u=i₁∘κ_Z.
symbol one_cat_native_window_snake_cycles_forward_reconstruction [K C : Cat] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
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
  C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1))
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C
  C1 t (@additive_terminal_object C Prod t Add) R1) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1)) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R1)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1))) (@one_cat_native_window_snake_cycles_forward_zero K C
  C1 Prod t Add T0 P R1 R2 m1));

// The first native product projection of c∘κ_c=0 supplies the original annihilation.
symbol one_cat_native_window_snake_cycles_kernel_first_zero [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero)
  C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1)))) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add)
  T0 (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C
  Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R2 walking_arrow_src)) (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (λ v : τ (@Transf K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) v (@kernel_adjunction_family_inclusion_transf
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))))) _ _ (@eq_sym _ _ _
  (@one_cat_product_family_pair_proj1_path K C C1 Prod (@additive_binary_products C Prod t Add)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R1)))) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@one_cat_product_family_proj1 K C C1 Prod (@additive_binary_products C Prod t Add)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@fapp0 (Functor_cat K (Product_cat
  C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ :
  τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt)))) (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func
  K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func
  K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@one_cat_product_family_proj1 K C C1 Prod (@additive_binary_products C Prod t Add)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)) v))
  _ _ (@one_cat_kernel_family_annihilation_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1)))) (@one_cat_zero_family_postcompose_path K C C1 t (@additive_terminal_object C
  Prod t Add) T0 (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func
  K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@one_cat_product_family_proj1 K C C1 Prod (@additive_binary_products C Prod t Add)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_tgt))))));

// The second native product projection of c∘κ_c=0 supplies the original annihilation.
symbol one_cat_native_window_snake_cycles_kernel_second_zero [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero)
  C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R1) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))) (@zero_arrow_family_zero_transf K C
  t (@additive_terminal_object C Prod t Add) T0 (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_tgt)))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C
  Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R1 walking_arrow_tgt)) (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_tgt)) (λ v : τ (@Transf K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt) v (@kernel_adjunction_family_inclusion_transf
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))))) _ _ (@eq_sym _ _ _
  (@one_cat_product_family_pair_proj2_path K C C1 Prod (@additive_binary_products C Prod t Add)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R1)))) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)
  (@one_cat_product_family_proj2 K C C1 Prod (@additive_binary_products C Prod t Add)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@fapp0 (Functor_cat K (Product_cat
  C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ :
  τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt)))) (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_tgt)) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func
  K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func
  K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)
  (@one_cat_product_family_proj2 K C C1 Prod (@additive_binary_products C Prod t Add)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)) v))
  _ _ (@one_cat_kernel_family_annihilation_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1)))) (@one_cat_zero_family_postcompose_path K C C1 t (@additive_terminal_object C
  Prod t Add) T0 (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func
  K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)
  (@one_cat_product_family_proj2 K C C1 Prod (@additive_binary_products C Prod t Add)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_tgt))))));

// The original row lift sends K(c) into A₁; it retains the original row and its kernel inverse.
symbol one_cat_native_window_snake_cycles_row_lift [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (E1 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R1))
  : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R1))
≔ (@one_cat_short_exact_family_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_diagram_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@one_cat_zero_cone_row_family_transf K C C1 t (@additive_terminal_object C Prod t Add) R1) E1
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_window_snake_cycles_kernel_second_zero K C C1 Prod t Add T0 P
  R1 R2 m1));

// The whole row lift reconstructs i₁∘v₀=κ_c.
symbol one_cat_native_window_snake_cycles_row_reconstruction [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero)
  C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (E1 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R1))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C
  C1 t (@additive_terminal_object C Prod t Add) R1) (@one_cat_native_window_snake_cycles_row_lift K C C1 Prod
  t Add T0 P Q R1 R2 m1 E1)) (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))))
≔ (@one_cat_short_exact_family_lift_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_diagram_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@one_cat_zero_cone_row_family_transf K C C1 t
  (@additive_terminal_object C Prod t Add) R1) E1 (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_window_snake_cycles_kernel_second_zero K C C1 Prod t Add T0 P
  R1 R2 m1));

// The next row inclusion reflects the derived zero, so the whole row lift lands in left cycles.
symbol one_cat_native_window_snake_cycles_row_cycle_zero [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (E1 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R1))
  (E2 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R2))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R2)) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R1) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R2)
  (@zero_cone_row_family_source_map K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)
  (@one_cat_native_window_snake_cycles_row_lift K C C1 Prod t Add T0 P Q R1 R2 m1 E1))
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R2)))
≔ (@one_cat_short_exact_family_incoming_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R2) (@zero_cone_row_family_diagram_func K C t
  (@additive_terminal_object C Prod t Add) R2) (@one_cat_zero_cone_row_family_transf K C C1 t
  (@additive_terminal_object C Prod t Add) R2) E2 (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R2) (@zero_cone_row_family_source_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1) (@one_cat_native_window_snake_cycles_row_lift K C C1 Prod
  t Add T0 P Q R1 R2 m1 E1)) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R2)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R2) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C
  C1 t (@additive_terminal_object C Prod t Add) R2) (@zero_cone_row_family_source_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1) (@one_cat_native_window_snake_cycles_row_lift K C C1 Prod
  t Add T0 P Q R1 R2 m1 E1)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)) (@Transf K C (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)) (λ v : τ (@Transf K C
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R1) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2
  walking_arrow_src) v (@one_cat_native_window_snake_cycles_row_lift K C C1 Prod t Add T0 P Q R1 R2 m1 E1))) _
  _ (@eq_sym _ _ _ (@one_cat_zero_cone_row_incoming_square_path K C C1 t (@additive_terminal_object C Prod t
  Add) R1 R2 m1))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming
  K C C1 t (@additive_terminal_object C Prod t Add) R1) (@one_cat_native_window_snake_cycles_row_lift K C C1
  Prod t Add T0 P Q R1 R2 m1 E1))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) v)) _ _
  (@one_cat_native_window_snake_cycles_row_reconstruction K C C1 Prod t Add T0 P Q R1 R2 m1 E1)) (@eq_trans _
  _ _ _ (@one_cat_native_window_snake_cycles_kernel_first_zero K C C1 Prod t Add T0 P R1 R2 m1) (@eq_sym _ _ _
  (@one_cat_zero_family_postcompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R2) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C
  C1 t (@additive_terminal_object C Prod t Add) R2)))))))));

// v:K(c)⇒Z(A₁) is the original whole kernel mate of that row lift.
symbol one_cat_native_window_snake_cycles_backward [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (E1 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R1))
  (E2 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R2))
  : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)))
≔ (@one_cat_kernel_family_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod
  t
  Add) T0 P (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t
  Add) R1 R2 m1) (@one_cat_native_window_snake_cycles_row_lift K C C1 Prod t Add T0 P Q R1 R2 m1 E1)
  (@one_cat_native_window_snake_cycles_row_cycle_zero K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2));

// The original left-cycle inclusion reconstructs κ_Z∘v=v₀.
symbol one_cat_native_window_snake_cycles_backward_reconstruction [K C : Cat] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (E1 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R1))
  (E2 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R2))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R1)) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
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
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2))
  (@one_cat_native_window_snake_cycles_row_lift K C C1 Prod t Add T0 P Q R1 R2 m1 E1))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t
  Add) R1 R2 m1) (@one_cat_native_window_snake_cycles_row_lift K C C1 Prod t Add T0 P Q R1 R2 m1 E1)
  (@one_cat_native_window_snake_cycles_row_cycle_zero K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2));

// Whole row and kernel cancellation prove v∘u=id at the original left cycles.
symbol one_cat_native_window_snake_cycles_backward_forward [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (E1 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R1))
  (E2 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R2))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)))
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)) (@id (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1) (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)) (@id (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)))
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@one_cat_native_window_snake_cycles_backward K C C1
  Prod t Add T0 P Q R1 R2 m1 E1 E2) (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2
  m1)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R1)) (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1)) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R1)), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R1) v (@one_cat_native_window_snake_cycles_forward K C C1 Prod
  t Add T0 P R1 R2 m1))) _ _ (@one_cat_native_window_snake_cycles_backward_reconstruction K C C1 Prod t Add T0
  P Q R1 R2 m1 E1 E2)) (@one_cat_short_exact_family_incoming_reflect_path K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_diagram_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@one_cat_zero_cone_row_family_transf K C C1 t
  (@additive_terminal_object C Prod t Add) R1) E1 (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R1) (@one_cat_native_window_snake_cycles_row_lift K C C1 Prod t
  Add T0 P Q R1 R2 m1 E1) (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
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
  t Add T0 P Q R1 R2 m1 E1) (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) v
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1))) _ _
  (@one_cat_native_window_snake_cycles_row_reconstruction K C C1 Prod t Add T0 P Q R1 R2 m1 E1))
  (@one_cat_native_window_snake_cycles_forward_reconstruction K C C1 Prod t Add T0 P R1 R2 m1)))))));

// Whole kernel cancellation proves u∘v=id at the original K(c).
symbol one_cat_native_window_snake_cycles_forward_backward [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (E1 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R1))
  (E2 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R2))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1)))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)) (@id (Functor_cat K
  C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)) (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)) (@id (Functor_cat K
  C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))) (@eq_trans
  _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
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
  C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (@Transf K C (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) v
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2))) _ _
  (@one_cat_native_window_snake_cycles_forward_reconstruction K C C1 Prod t Add T0 P R1 R2 m1)) (@eq_trans _ _
  _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C
  C1 t (@additive_terminal_object C Prod t Add) R1) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R1)) (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R1)), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R1) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add)
  R1) v)) _ _ (@one_cat_native_window_snake_cycles_backward_reconstruction K C C1 Prod t Add T0 P Q R1 R2 m1
  E1 E2)) (@one_cat_native_window_snake_cycles_row_reconstruction K C C1 Prod t Add T0 P Q R1 R2 m1 E1))))));

// Fixed-forward ΩAlong(u), with the same derived v in both native inverse slots.
symbol one_cat_native_window_snake_cycles_equiv [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (E1 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R1))
  (E2 : τ (@OneCatZeroConeShortExactFamily K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q R2))
  : τ (@OmegaEquivAlong (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1))
≔ (@omega_equiv_along_intro (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)
  (@one_cat_native_window_snake_cycles_backward_forward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)
  (@one_cat_native_window_snake_cycles_forward_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2));
