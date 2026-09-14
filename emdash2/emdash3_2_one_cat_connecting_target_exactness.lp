require open emdash.emdash3_2_one_cat_connecting_target_lifts;
require open emdash.emdash3_2_one_cat_image_kernel_exactness;

// The original target exactness input retains the whole connecting transformation δ.
symbol one_cat_target_boundary_inclusion_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object
  C Prod t A)) Rm R0)) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R0 R1))
  (m1 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R1 R2)) (upper_zero : τ (@=
  (@Transf B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R1 walking_arrow_src)))) (lower_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)))) (Em : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R2))
 : τ (@= (@Transf B C (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))
  (@one_cat_native_window_connecting_transf B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2))
≔ @one_cat_kernel_input_boundary_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_connecting_transf B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_incoming_connecting_zero B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2);

// The original target homology boundary reconstructs the two original covers on the preimage.
symbol one_cat_target_boundary_cover_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object
  C Prod t A)) Rm R0)) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R0 R1))
  (m1 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R1 R2)) (upper_zero : τ (@=
  (@Transf B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R1 walking_arrow_src)))) (lower_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)))) (Em : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R2))
 : τ (@= (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)))) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func
  B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_target_homology_preimage B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2)) (@one_cat_target_cover_composite B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2))
≔ @one_cat_kernel_family_inclusion_reflect_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_target_homology_preimage B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2)) (@one_cat_target_cover_composite B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_target_homology_preimage B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2)) (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2)) (λ v : τ (@Transf B C (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A)
  C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)),
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2) v (@one_cat_target_homology_preimage B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))
  (@one_cat_native_window_connecting_transf B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2) (@one_cat_target_boundary_inclusion_path B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_target_preimage_reconstruction B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)));

// The two derived original covers cancel as a whole composite.
symbol one_cat_target_cover_composite_reflect_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object
  C Prod t A)) Rm R0)) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R0 R1))
  (m1 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R1 R2)) (upper_zero : τ (@=
  (@Transf B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R1 walking_arrow_src)))) (lower_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)))) (Em : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R2)) (Y : τ (Functor B C)) (u v : τ (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) Y)) (e : τ (@= (@Transf B C (@one_cat_target_boundary_cover_func B C
  C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) Y) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) Y u (@one_cat_target_cover_composite
  B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) Y v (@one_cat_target_cover_composite
  B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) Y) u v)
≔ @one_cat_target_class_cover_reflect_path B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2 Y u v (@one_cat_target_boundary_cover_reflect_path B C C1 Prod t A T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2 Y (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) Y u (@one_cat_target_class_projection
  B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) Y v (@one_cat_target_class_projection
  B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_sym _
  _ _ (@comp_assoc (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) Y u (@one_cat_target_class_projection B C C1 Prod t A T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ e (@comp_assoc (Functor_cat B
  C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) Y v (@one_cat_target_class_projection B C C1 Prod t A T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))));

// The original target boundary quotient vanishes after the two derived covers.
symbol one_cat_target_boundary_quotient_cover_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object
  C Prod t A)) Rm R0)) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R0 R1))
  (m1 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R1 R2)) (upper_zero : τ (@=
  (@Transf B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R1 walking_arrow_src)))) (lower_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)))) (Em : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R2))
 : τ (@= (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_target_cover_composite B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)))) (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (λ v : τ (@Transf B C
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))), (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) v)) (@one_cat_target_cover_composite B C C1 Prod t A T0 P
  Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_target_homology_preimage B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2)) (@eq_sym _ _ _ (@one_cat_target_boundary_cover_path B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_target_homology_preimage B C C1 Prod t A T0 P Q
  N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@Transf B C (@one_cat_target_boundary_cover_func B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (λ v : τ (@Transf B C
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))), (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) v (@one_cat_target_homology_preimage B C C1 Prod t A T0 P
  Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))
  (@one_cat_cokernel_family_annihilation_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 Q (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))) (@one_cat_zero_family_precompose_path B C C1 t
  (@additive_terminal_object C Prod t A) T0 (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_target_homology_preimage B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2)))));

// Cancel the original covers to prove zero of the actual target boundary quotient.
symbol one_cat_target_boundary_quotient_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object
  C Prod t A)) Rm R0)) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R0 R1))
  (m1 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R1 R2)) (upper_zero : τ (@=
  (@Transf B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R1 walking_arrow_src)))) (lower_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)))) (Em : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R2))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))
  (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@zero_arrow_family_zero_transf
  B C t (@additive_terminal_object C Prod t A) T0 (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))))
≔ @one_cat_target_cover_composite_reflect_path B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2 (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@zero_arrow_family_zero_transf
  B C t (@additive_terminal_object C Prod t A) T0 (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _
  (@one_cat_target_boundary_quotient_cover_zero B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@eq_sym _ _ _ (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object
  C Prod t A) T0 (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_target_cover_composite B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2))));

// The derived boundary quotient zero certifies the original Im(δ)⇒K(H(i)) comparison.
symbol one_cat_native_window_target_exact_omega [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
  τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object
  C Prod t A)) Rm R0)) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R0 R1))
  (m1 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R1 R2)) (upper_zero : τ (@=
  (@Transf B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R1 walking_arrow_src)))) (lower_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)))) (Em : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R2))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@zero_arrow_family_incoming_func B C t (@additive_terminal_object C Prod t A)
  (@one_cat_native_window_source_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@one_cat_native_window_target_exact_comparison B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
≔ @one_cat_image_kernel_exact_from_boundary_zero B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) N
  (@one_cat_target_boundary_quotient_zero B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2);
