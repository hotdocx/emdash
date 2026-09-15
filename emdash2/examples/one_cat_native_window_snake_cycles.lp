/* Actual whole consumers of the original cycle comparison.
   Source checking proves the named lemmas; this reviewer exercises selected
   data, arbitrary whole-map cancellation and reconstruction after composition. */
require open emdash.emdash3_2_one_cat_native_window_snake_cycles;

// Recover the same derived left inverse, through the existing ΩAlong consumer.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (@additive_terminal_object C Prod t Add) T0 P Q R2)) ⊢ (@omega_equiv_along_left_inv (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_equiv K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)) ≡
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2);

// Recover the same derived right inverse, through the existing ΩAlong consumer.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (@additive_terminal_object C Prod t Add) T0 P Q R2)) ⊢ (@omega_equiv_along_right_inv (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_equiv K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)) ≡
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2);

// The recovered inverse retains its arbitrary-base Hom action.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (x y : τ (Obj K)) ⊢ (@tapp1_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) x y (@omega_equiv_along_left_inv (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_equiv K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2))) ≡ (@tapp1_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)) x y
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2));

// Apply native left cancellation to an arbitrary original whole map h.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (F : τ (Functor K C)) (h : τ (@Transf K C F (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)))) ⊢ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) F
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
  (@omega_equiv_along_left_inv (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_equiv K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1) h) (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)))
  (@Transf K C F (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1))) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))),
  (@comp_fapp0 (Functor_cat K C) F (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)) v h)) _ _
  (@omega_equiv_along_left_law (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_equiv K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)))) : τ (@= (@Transf K C
  F (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2
  m1))) (@comp_fapp0 (Functor_cat K C) F (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@omega_equiv_along_left_inv (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_equiv K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)) (@comp_fapp0
  (Functor_cat K C) F (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1) h)) h);

// Apply native right cancellation to an arbitrary original whole map h.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (F : τ (Functor K C)) (h : τ (@Transf K C F (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))))) ⊢ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) F
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
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
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1) (@omega_equiv_along_right_inv
  (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
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
  (@one_cat_native_window_snake_cycles_equiv K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)) h) (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))) (@Transf K C F
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))), (@comp_fapp0 (Functor_cat K C) F
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) v h)) _ _
  (@omega_equiv_along_right_law (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_equiv K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)))) : τ (@= (@Transf K C
  F (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))))
  (@comp_fapp0 (Functor_cat K C) F (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1) (@comp_fapp0 (Functor_cat K C)
  F (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@omega_equiv_along_right_inv (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_equiv K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)) h)) h);

// Restrict the forward comparison to an arbitrary original whole incoming map.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add)))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (F : τ (Functor K C)) (h : τ (@Transf K C F (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)))) ⊢ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) F
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
  C1 Prod t Add T0 R1 R2 m1))) (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  h) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (@Transf K C F
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (λ
  v : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat K C) F
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) v
  h)) _ _ (@one_cat_native_window_snake_cycles_forward_reconstruction K C C1 Prod t Add T0 P R1 R2 m1))
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) F (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C
  C1 t (@additive_terminal_object C Prod t Add) R1) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)) h)))) : τ
  (@= (@Transf K C F (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) F (@kernel_adjunction_family_func K C
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
  C1 Prod t Add T0 R1 R2 m1))) (@comp_fapp0 (Functor_cat K C) F (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1) h)) (@comp_fapp0 (Functor_cat
  K C) F (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R1) (@comp_fapp0
  (Functor_cat K C) F (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)) h)));

// Both original inclusions reconstruct an arbitrary whole map after the selected inverse.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (F : τ (Functor K C)) (h : τ (@Transf K C F (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))))) ⊢ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C F
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)) (@Transf K C F
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (λ
  v : τ (@Transf K C F (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)),
  (@comp_fapp0 (Functor_cat K C) F (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod
  t Add) R1) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add)
  R1) v)) _ _ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) F (@kernel_adjunction_family_func K C
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
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@omega_equiv_along_left_inv (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_equiv K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)) h) (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R1)) (@Transf K C F (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1)) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R1)), (@comp_fapp0 (Functor_cat K C) F
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_source_func K
  C t (@additive_terminal_object C Prod t Add) R1) v h)) _ _
  (@one_cat_native_window_snake_cycles_backward_reconstruction K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2))))
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) F (@kernel_adjunction_family_func K C
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
  t Add T0 P Q R1 R2 m1 E1) h) (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@Transf K C F (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat K C) F
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) v h)) _ _
  (@one_cat_native_window_snake_cycles_row_reconstruction K C C1 Prod t Add T0 P Q R1 R2 m1 E1)))) : τ (@=
  (@Transf K C F (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) F (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming K C
  C1 t (@additive_terminal_object C Prod t Add) R1) (@comp_fapp0 (Functor_cat K C) F
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@comp_fapp0 (Functor_cat K C) F
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1))
  (@omega_equiv_along_left_inv (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_equiv K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)) h))) (@comp_fapp0
  (Functor_cat K C) F (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) h));

// A different arbitrary map is not identified with the selected inverse.
assertnot [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  (w : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C
  C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)))) ⊢ (@eq_refl (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_backward K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)) : τ (@= (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object
  C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@zero_cone_left_column_outgoing_func K C t (@additive_terminal_object C Prod t Add) R1 R2 m1)))
  (@omega_equiv_along_left_inv (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@zero_cone_left_column_outgoing_func K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)))
  (@one_cat_native_window_snake_cycles_forward K C C1 Prod t Add T0 P R1 R2 m1)
  (@one_cat_native_window_snake_cycles_equiv K C C1 Prod t Add T0 P Q R1 R2 m1 E1 E2)) w);
