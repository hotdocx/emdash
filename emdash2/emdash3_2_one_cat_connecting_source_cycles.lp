require open emdash.emdash3_2_one_cat_connecting_source_representatives;
require open emdash.emdash3_2_one_cat_additive_family_units;
require open emdash.emdash3_2_one_cat_additive_family_cancellation;
require open emdash.emdash3_2_one_cat_kernel_input_boundaries;
require open emdash.emdash3_2_one_cat_row_homology_maps;

// The original left boundary reconstructs the original incoming left differential.
symbol one_cat_source_left_boundary_ambient_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
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
 : τ (@= (@Transf B C (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)) (@comp_fapp0 (Functor_cat B
  C) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_native_window_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@zero_cone_row_family_source_map B
  C t (@additive_terminal_object C Prod t A) R0 R1 m0))
≔ @one_cat_kernel_input_boundary_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@zero_cone_row_family_source_func B C t (@additive_terminal_object
  C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_row_family_source_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_left_column_zero_path B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2);

// The same original boundary reconstructs the left cycle on the composite representative.
symbol one_cat_source_boundary_cycle_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
 : τ (@= (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1))) (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_boundary_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_source_func
  B C t (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_native_window_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_source_boundary_representative B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_source_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@one_cat_source_cover_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_source_boundary_projection B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2))))
≔ (@eq_trans _ _ _ _ (@one_cat_source_boundary_reconstruction B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C)
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_source_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2) (@one_cat_source_cover_representative B C C1 Prod t A T0 P Q
  N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_boundary_projection B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))));

// Original row and kernel reconstruction identify the covered middle differential.
symbol one_cat_source_covered_differential_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
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
 : τ (@= (@Transf B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src))
  (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src)
  (@kernel_precomposition_first_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))) (@comp_fapp0 (Functor_cat B
  C) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1) (@comp_fapp0
  (Functor_cat B C) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2))))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@one_cat_native_cover_left_reconstruction B C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 m0 E1)) (@eq_ap (@Transf B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)) (@Transf B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)) (λ v : τ
  (@Transf B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)), (@comp_fapp0 (Functor_cat
  B C) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1) v))
  (@one_cat_native_cover_left_lift B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R0 R1 m0 E1) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R1) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)) (@eq_sym _ _ _ (@one_cat_native_cover_cycles_reconstruction B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E1 E2))));

// The original L projection gives the retained whole middle lift.
symbol one_cat_source_middle_lift [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ
  (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0
  P Q)) (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)))) (mm : τ
  (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) Rm R0)) (m0 : τ (@Transf B
  (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C
  t (@additive_terminal_object C Prod t A)) R1 R2)) (upper_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src))
  (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) Rm R0 mm
  walking_arrow_src)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R2 walking_arrow_src)))) (Em : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0)) (E1 : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R2))
 : τ (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R0 walking_arrow_src))
≔ (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R0 walking_arrow_src) (@kernel_precomposition_first_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@one_cat_source_cover_representative B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_boundary_projection B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)));

// The original incoming row map sends the left boundary representative to the middle object.
symbol one_cat_source_middle_correction [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
 : τ (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R0 walking_arrow_src))
≔ (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object
  C Prod t A) R0) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_source_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2));

// The original middle lift and correction have the same whole differential.
symbol one_cat_source_middle_differential_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
 : τ (@= (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src) (@one_cat_source_middle_lift B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src) (@one_cat_source_middle_correction B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src) (@kernel_precomposition_first_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@one_cat_source_cover_representative B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_boundary_projection B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)) (@Transf
  B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src) v
  (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_class_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@one_cat_source_cover_representative B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_boundary_projection B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src)
  (@kernel_precomposition_first_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))) (@comp_fapp0 (Functor_cat B
  C) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1) (@comp_fapp0
  (Functor_cat B C) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2))) (@one_cat_source_covered_differential_path B C C1 Prod t A
  T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1) (@comp_fapp0
  (Functor_cat B C) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_source_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@one_cat_source_cover_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_source_boundary_projection B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@one_cat_source_boundary_cover_func B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)) (@Transf B C
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R1)), (@comp_fapp0 (Functor_cat B C)
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1) v)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1) (@comp_fapp0 (Functor_cat B
  C) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_source_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@one_cat_source_cover_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_source_boundary_projection B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@one_cat_native_cover_left_cycles B C (@additive_preadditive
  C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2) (@comp_fapp0
  (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@one_cat_source_cover_representative B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_boundary_projection B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))) (@eq_sym _ _ _ (@comp_assoc (Functor_cat B
  C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_source_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@one_cat_source_cover_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_source_boundary_projection B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2))))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@one_cat_source_boundary_cover_func B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))) (@Transf B C
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1))), (@comp_fapp0 (Functor_cat B C)
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1) (@comp_fapp0
  (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)) v)))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@one_cat_native_cover_left_cycles B C (@additive_preadditive
  C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2) (@comp_fapp0
  (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@one_cat_source_cover_representative B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_boundary_projection B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_native_window_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_source_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2)) (@eq_sym _ _ _ (@one_cat_source_boundary_cycle_path B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)) (@Transf B C
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R1)), (@comp_fapp0 (Functor_cat B C)
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1) v)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object
  C Prod t A) R0) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_source_func B C t (@additive_terminal_object C
  Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_native_window_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_source_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C
  Prod t A) R1) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t (@additive_terminal_object
  C Prod t A) R0) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_native_window_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))
  (@one_cat_source_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2)) (@comp_assoc (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R1) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_native_window_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_source_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C
  Prod t A) R1)) (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm
  m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R1 walking_arrow_src)) (λ v : τ (@Transf B C (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C
  Prod t A) R1)), (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q
  N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R1) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C
  Prod t A) R1) (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C
  Prod t A) R1) v (@one_cat_source_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R1) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_native_window_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@zero_cone_row_family_source_map B
  C t (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_source_left_boundary_ambient_path B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t
  A) R0) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_source_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_source_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R1 walking_arrow_src)) (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q
  N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src)) (λ v : τ (@Transf B C
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)),
  (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object
  C Prod t A) R0) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) v (@one_cat_source_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C
  Prod t A) R1) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_source_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0)) (@comp_fapp0
  (Functor_cat B C) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R0)) (@eq_sym _ _ _
  (@one_cat_zero_cone_row_incoming_square_path B C C1 t (@additive_terminal_object C Prod t A) R0 R1 m0)))
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q
  N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_source_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2))))))))))));

// The original whole difference corrects the retained middle lift.
symbol one_cat_source_corrected_middle_transf [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
 : τ (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R0 walking_arrow_src))
≔ @one_cat_difference_family B C C1 Prod t A T0 (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q
  N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@one_cat_source_middle_lift B C C1 Prod t A
  T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_middle_correction B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2);

// Whole difference bilinearity makes the corrected middle lift a cycle.
symbol one_cat_source_corrected_middle_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
 : τ (@= (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src)
  (@one_cat_source_corrected_middle_transf B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)))
≔ @one_cat_difference_family_postcompose_zero_path B C C1 Prod t A T0 (@one_cat_source_boundary_cover_func B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_source_middle_lift B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2) (@one_cat_source_middle_correction B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src) (@one_cat_source_middle_differential_path B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2);

// The native K mate lifts the corrected map into the original upper middle cycle object.
symbol one_cat_source_middle_cycle [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ
  (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0
  P Q)) (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)))) (mm : τ
  (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) Rm R0)) (m0 : τ (@Transf B
  (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C
  t (@additive_terminal_object C Prod t A)) R1 R2)) (upper_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src))
  (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) Rm R0 mm
  walking_arrow_src)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R2 walking_arrow_src)))) (Em : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0)) (E1 : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R2))
 : τ (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)))
≔ @one_cat_kernel_family_lift B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A)
  T0 P (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0
  R1 m0) (@one_cat_source_corrected_middle_transf B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_source_corrected_middle_zero B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2);

// The original upper middle kernel inclusion recovers the same corrected map.
symbol one_cat_source_middle_cycle_reconstruction [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
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
 : τ (@= (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R0 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@one_cat_source_middle_cycle B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2)) (@one_cat_source_corrected_middle_transf B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2))
≔ @one_cat_kernel_family_lift_ambient_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_source_corrected_middle_transf B C C1 Prod t A
  T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_corrected_middle_zero B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2);

// The original row zero law annihilates the correction under its outgoing projection.
symbol one_cat_source_correction_projection_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
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
 : τ (@= (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R0 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0) (@one_cat_source_middle_correction B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R0 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_source_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_tgt)) (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q
  N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)) (λ v : τ (@Transf B C
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)),
  (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object
  C Prod t A) R0) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_tgt) v (@one_cat_source_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R0 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R0))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt))
  (@one_cat_zero_family_chain_path B C C1 t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_row_family_diagram_func B C t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_zero_cone_row_family_transf B C C1 t (@additive_terminal_object C Prod t A) R0)))
  (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@one_cat_source_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2))));

// The whole difference unit law preserves the original outgoing projection.
symbol one_cat_source_corrected_projection_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
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
 : τ (@= (@Transf B C (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R0 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@one_cat_source_boundary_cover_func B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0) (@one_cat_source_corrected_middle_transf B C C1 Prod t A T0 P Q
  N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_source_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_source_middle_lift B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2)))
≔ @one_cat_difference_killed_second_path B C C1 Prod t A T0 (@one_cat_source_boundary_cover_func B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@one_cat_source_middle_lift B C C1 Prod t A
  T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_source_middle_correction B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0) (@one_cat_source_correction_projection_zero B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2);
