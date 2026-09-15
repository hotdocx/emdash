/* The actual window input feeds the original whole P/Q snake factors. */
require open emdash.emdash3_2_one_cat_native_window_snake_inputs;
require open emdash.emdash3_2_one_cat_native_snake_factors;

assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
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
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)))) ⊢ (@one_cat_native_snake_alpha K C
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)) : τ
  (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat
  C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))));
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
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
  (x : τ (Obj K)) ⊢ (@tapp0_fapp0 K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) x (@one_cat_native_snake_alpha K C
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) : τ
  (Hom C (@fapp0 K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0))) x) (@fapp0 K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) x));
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
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
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)))) ⊢ (@one_cat_native_snake_gamma K C
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)) : τ
  (@Transf K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
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
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))));
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
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
  (x : τ (Obj K)) ⊢ (@tapp0_fapp0 K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)))
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) x (@one_cat_native_snake_gamma K C
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) : τ
  (Hom C (@fapp0 K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
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
  (@one_cat_native_window_snake_input K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero))) x)
  (@fapp0 K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C
  C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  x));
