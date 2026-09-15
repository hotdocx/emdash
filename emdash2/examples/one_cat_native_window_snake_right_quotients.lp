/* Actual whole quotient, row-colift and γ-diagram consumers. */
require open emdash.emdash3_2_one_cat_native_window_snake_right_gamma;

// Native left inverse data retains the original second quotient descent.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (@additive_terminal_object C Prod t Add) T0 P Q R0)) ⊢ (@omega_equiv_along_left_inv (Functor_cat K C)
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
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_equiv K C C1 Prod t Add T0 P Q Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) ≡ (@one_cat_native_window_snake_right_quotient_backward K C
  C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0);

// Native right inverse data retains the original second quotient descent.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (@additive_terminal_object C Prod t Add) T0 P Q R0)) ⊢ (@omega_equiv_along_right_inv (Functor_cat K C)
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
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_equiv K C C1 Prod t Add T0 P Q Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) ≡ (@one_cat_native_window_snake_right_quotient_backward K C
  C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0);

// The selected inverse retains its whole Hom action.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (x y : τ (Obj K)) ⊢ (@tapp1_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) x y
  (@omega_equiv_along_left_inv (Functor_cat K C) (@cokernel_adjunction_family_func K C (@additive_preadditive
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
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_equiv K C C1 Prod t Add T0 P Q Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0))) ≡ (@tapp1_func K C (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@cokernel_adjunction_family_func K C
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
  upper_zero lower_zero))) x y (@one_cat_native_window_snake_right_quotient_backward K C C1 Prod t Add T0 P Q
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0));

// Apply left inverse cancellation to an arbitrary whole map.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (J : τ (Functor K C)) (h : τ (@Transf K C J (@cokernel_adjunction_family_func K C (@additive_preadditive C
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))) ⊢
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) J (@cokernel_adjunction_family_func K C
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
  (@omega_equiv_along_left_inv (Functor_cat K C) (@cokernel_adjunction_family_func K C (@additive_preadditive
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
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_equiv K C C1 Prod t Add T0 P Q Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) (@one_cat_native_window_snake_right_quotient_forward K C C1
  Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0) h) (@eq_ap (@Transf K C
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
  (@Transf K C J (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
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
  (@comp_fapp0 (Functor_cat K C) J (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) v h))
  _ _ (@omega_equiv_along_left_law (Functor_cat K C) (@cokernel_adjunction_family_func K C
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
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_equiv K C C1 Prod t Add T0 P Q Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)))) : τ (@= (@Transf K C J (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t
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
  upper_zero lower_zero)))) (@comp_fapp0 (Functor_cat K C) J (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@cokernel_adjunction_family_func K C
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
  upper_zero lower_zero))) (@omega_equiv_along_left_inv (Functor_cat K C) (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t
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
  upper_zero lower_zero))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_equiv K C C1 Prod t Add T0 P Q Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) (@comp_fapp0 (Functor_cat K C) J
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
  upper_zero lower_zero Em E0) h)) h);

// Apply right inverse cancellation to an arbitrary whole map.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (J : τ (Functor K C)) (h : τ (@Transf K C J (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm
  R0 mm)))) ⊢ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) J (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@cokernel_adjunction_family_func K C
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
  upper_zero lower_zero Em E0) (@omega_equiv_along_right_inv (Functor_cat K C)
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
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_equiv K C C1 Prod t Add T0 P Q Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) h) (@eq_ap (@Transf K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm))) (@Transf K C J (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm))) (λ v : τ (@Transf K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm))), (@comp_fapp0 (Functor_cat K C) J
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm)) v h)) _ _
  (@omega_equiv_along_right_law (Functor_cat K C) (@cokernel_adjunction_family_func K C (@additive_preadditive
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
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_equiv K C C1 Prod t Add T0 P Q Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)))) : τ (@= (@Transf K C J (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm))) (@comp_fapp0 (Functor_cat K C) J
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
  upper_zero lower_zero Em E0) (@comp_fapp0 (Functor_cat K C) J (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@cokernel_adjunction_family_func K C
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
  upper_zero lower_zero))) (@omega_equiv_along_right_inv (Functor_cat K C) (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t
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
  upper_zero lower_zero))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_equiv K C C1 Prod t Add T0 P Q Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) h)) h);

// Retain the original quotient or row map after arbitrary whole precomposition.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (J : τ (Functor K C)) (h : τ (@Transf K C J (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src))) ⊢ (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat K C) J (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) h)
  (@eq_ap (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))) (@Transf K
  C J (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))) (λ v : τ
  (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))),
  (@comp_fapp0 (Functor_cat K C) J (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0
  Q (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm)) v h)) _ _
  (@one_cat_native_window_snake_right_quotient_forward_reconstruction K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm
  m0 m1 upper_zero lower_zero Em E0))) : τ (@= (@Transf K C J (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm))) (@comp_fapp0 (Functor_cat K C) J
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
  upper_zero lower_zero Em E0) (@comp_fapp0 (Functor_cat K C) J (@zero_cone_row_family_vertex_func K C t
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
  upper_zero lower_zero))) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t
  Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) h))
  (@comp_fapp0 (Functor_cat K C) J (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0
  Q (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0)) h));

// Retain the original quotient or row map after arbitrary whole precomposition.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (J : τ (Functor K C)) (h : τ (@Transf K C J (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt))) ⊢ (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat K C) J (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
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
  R0 mm)) h) (@eq_ap (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))
  (@Transf K C J (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
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
  (@comp_fapp0 (Functor_cat K C) J (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0
  Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) v h))
  _ _ (@one_cat_native_window_snake_right_quotient_backward_reconstruction K C C1 Prod t Add T0 P Q Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0))) : τ (@= (@Transf K C J (@cokernel_adjunction_family_func K C
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
  upper_zero lower_zero)))) (@comp_fapp0 (Functor_cat K C) J (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@cokernel_adjunction_family_func K C
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
  upper_zero lower_zero))) (@one_cat_native_window_snake_right_quotient_backward K C C1 Prod t Add T0 P Q Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0) (@comp_fapp0 (Functor_cat K C) J
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm)) h))
  (@comp_fapp0 (Functor_cat K C) J (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_tgt) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0
  Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
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
  lower_zero Em E0) h));

// Retain the original quotient or row map after arbitrary whole precomposition.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (J : τ (Functor K C)) (h : τ (@Transf K C J (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src))) ⊢ (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat K C) J (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
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
  (@one_cat_native_window_snake_right_row_colift K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R0) h)
  (@eq_ap (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
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
  (@Transf K C J (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
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
  (@comp_fapp0 (Functor_cat K C) J (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0
  Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) v h))
  _ _ (@one_cat_native_window_snake_right_row_colift_reconstruction K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0))) : τ (@= (@Transf K C J (@cokernel_adjunction_family_func K C
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
  upper_zero lower_zero)))) (@comp_fapp0 (Functor_cat K C) J (@zero_cone_row_family_vertex_func K C t
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
  mm m0 m1 upper_zero lower_zero Em E0) (@comp_fapp0 (Functor_cat K C) J (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_tgt) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R0) h)) (@comp_fapp0 (Functor_cat K C) J
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) h));

// The quotient comparison carries the original γ after arbitrary whole precomposition.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (J : τ (Functor K C)) (h : τ (@Transf K C J (@cokernel_adjunction_family_func K C (@additive_preadditive C
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))) ⊢
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) J (@cokernel_adjunction_family_func K C
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
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@fapp0
  (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_right_quotient_paired_outgoing K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0) h) (@eq_ap (@Transf K C (@cokernel_adjunction_family_func
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
  upper_zero lower_zero))) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))))
  (@Transf K C J (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))))
  (λ v : τ (@Transf K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
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
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))), (@comp_fapp0 (Functor_cat K C) J
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
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) v h)) _ _
  (@one_cat_native_window_snake_right_quotient_gamma_triangle K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0))) : τ (@= (@Transf K C J (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat
  K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C),
  Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_tgt)))) (@comp_fapp0 (Functor_cat K C) J (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K
  C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C),
  Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_tgt))) (@one_cat_native_window_snake_right_quotient_paired_outgoing K C C1 Prod t Add T0 P Q
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0) (@comp_fapp0 (Functor_cat K C) J
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
  upper_zero lower_zero Em E0) h)) (@comp_fapp0 (Functor_cat K C) J (@cokernel_adjunction_family_func K C
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
  upper_zero lower_zero))) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_snake_gamma K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod
  t Add) T0 Q (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C
  C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
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
  upper_zero lower_zero)) h));

// The native whole diagram map retains its src endpoint action.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (@additive_terminal_object C Prod t Add) T0 P Q R0)) ⊢ (@sym_transf_tapp0_transf K WalkingArrow_cat C
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
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
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_snake_gamma K C
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
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_right_quotient_paired_outgoing K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0)) (@one_cat_native_window_snake_right_quotient_gamma_diagram_map K C C1 Prod t
  Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0) walking_arrow_src) ≡
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0);

// The native whole diagram map retains its tgt endpoint action.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (@additive_terminal_object C Prod t Add) T0 P Q R0)) ⊢ (@sym_transf_tapp0_transf K WalkingArrow_cat C
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
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
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_snake_gamma K C
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
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_right_quotient_paired_outgoing K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0)) (@one_cat_native_window_snake_right_quotient_gamma_diagram_map K C C1 Prod t
  Add T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0) walking_arrow_tgt) ≡ (@id (Functor_cat K C)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))));

// A different arbitrary inverse is not silently identified with the original one.
assertnot [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (w : τ (@Transf K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))))) ⊢
  (@eq_refl (@Transf K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
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
  (@one_cat_native_window_snake_right_quotient_backward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0)) : τ (@= (@Transf K C (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@zero_cone_right_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm)) (@cokernel_adjunction_family_func K C
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
  upper_zero lower_zero)))) (@omega_equiv_along_left_inv (Functor_cat K C) (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t
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
  upper_zero lower_zero))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@zero_cone_right_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) Rm R0 mm))
  (@one_cat_native_window_snake_right_quotient_forward K C C1 Prod t Add T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0) (@one_cat_native_window_snake_right_quotient_equiv K C C1 Prod t Add T0 P Q Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0)) w);
