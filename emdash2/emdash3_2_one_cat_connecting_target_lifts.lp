require open emdash.emdash3_2_one_cat_connecting_target_representatives;
require open emdash.emdash3_2_one_cat_kernel_input_boundaries;
require open emdash.emdash3_2_one_cat_short_exact_family_lifts;

// The original middle boundary reconstructs the original incoming differential.
symbol one_cat_target_middle_boundary_ambient_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
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
 : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2
  m1) (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero))) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src))
≔ @one_cat_kernel_input_boundary_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C
  Prod t A) R1 R2 m1) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src) lower_zero;

// The original middle representative has differential equal to the covered left cycle inclusion.
symbol one_cat_target_middle_differential_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src)
  (@one_cat_target_middle_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R1) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C
  Prod t A) R1) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@one_cat_target_cycle_representative B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R1 walking_arrow_src)) (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src)) (λ v : τ (@Transf B C
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)),
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R1 walking_arrow_src) v (@one_cat_target_middle_boundary_representative B C C1 Prod t A T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2
  m1) (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero))) (@eq_sym _ _ _ (@one_cat_target_middle_boundary_ambient_path B C C1 Prod t A T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat
  B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2
  m1) (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero)) (@one_cat_target_middle_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)))
  (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1))), (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  v)) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2
  m1) (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero)) (@one_cat_target_middle_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm
  m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_target_cycle_representative B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_target_boundary_projection
  B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_target_boundary_reconstruction B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@one_cat_target_boundary_cover_func B C
  C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))) (@Transf B C
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1))), (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  v)) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_target_cycle_representative B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_target_boundary_projection
  B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@one_cat_target_cycle_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_target_cycle_representative B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection
  B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))) (@eq_trans _ _ _ _
  (@comp_assoc (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@one_cat_target_cycle_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)) (@Transf
  B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src) v
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@one_cat_target_cycle_representative B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)))
  (@one_cat_row_triple_incoming_cycle_projection_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@one_cat_target_cycle_representative B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))))))))));

// The original row zero law annihilates the original precomposed differential on this representative.
symbol one_cat_target_cover_lift_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
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
 : τ (@= (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R1 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C
  (@precomposed_diagram_family_func B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod
  t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A)
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@one_cat_target_middle_boundary_representative B C C1 Prod t A
  T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R1 walking_arrow_tgt)) (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)) (λ v : τ (@Transf B C
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)),
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R1 walking_arrow_tgt) v (@one_cat_target_middle_boundary_representative B C C1 Prod t A T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src))
  (@one_cat_zero_cone_row_outgoing_square_path B C C1 t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_target_boundary_cover_func B C
  C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R1) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C
  Prod t A) R0 R1 m0 walking_arrow_src) (@one_cat_target_middle_boundary_representative B C C1 Prod t A T0 P
  Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R1 walking_arrow_tgt)) (λ v : τ (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R1) v))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src) (@one_cat_target_middle_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm
  m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1) (@comp_fapp0
  (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@one_cat_target_cycle_representative B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))))
  (@one_cat_target_middle_differential_path B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R1)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1) (@comp_fapp0
  (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@one_cat_target_cycle_representative B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf
  B C (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)) (@Transf
  B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_tgt)) (λ v : τ (@Transf B C (@zero_cone_row_family_source_func B C t (@additive_terminal_object C
  Prod t A) R1) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A
  T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R1) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R1 walking_arrow_tgt) v (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C
  C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@one_cat_target_cycle_representative B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))))) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R1)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt))
  (@one_cat_zero_family_chain_path B C C1 t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_diagram_func B C t (@additive_terminal_object C Prod t A) R1)
  (@one_cat_zero_cone_row_family_transf B C C1 t (@additive_terminal_object C Prod t A) R1)))
  (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R1) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@one_cat_target_cycle_representative B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))))))));

// The native K mate lifts the original middle representative into the original L.
symbol one_cat_target_original_cover_lift [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
 : τ (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)))
≔ @one_cat_kernel_family_lift B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A)
  T0 P (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@precomposed_diagram_family_func B C (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@one_cat_target_middle_boundary_representative B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_cover_lift_zero B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2);

// The original first projection of L recovers the same middle representative.
symbol one_cat_target_original_cover_lift_reconstruction [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ
  (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
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
  upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R0 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod
  t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R0 walking_arrow_src) (@kernel_precomposition_first_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2)) (@one_cat_target_middle_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2))
≔ @one_cat_kernel_family_lift_ambient_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@precomposed_diagram_family_func B C
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@one_cat_target_middle_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_target_cover_lift_zero B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2);

// Original incoming-row cancellation identifies the left lift of the retained representative.
symbol one_cat_target_left_lift_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
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
 : τ (@= (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t
  A) R1)) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@zero_cone_row_family_source_func B C t (@additive_terminal_object
  C Prod t A) R1) (@one_cat_native_cover_left_lift B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 m0 E1) (@one_cat_target_original_cover_lift B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@one_cat_target_cycle_representative B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))))
≔ @one_cat_short_exact_family_incoming_reflect_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R1) (@zero_cone_row_family_diagram_func B C t (@additive_terminal_object
  C Prod t A) R1) (@one_cat_zero_cone_row_family_transf B C C1 t (@additive_terminal_object C Prod t A) R1) E1
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@zero_cone_row_family_source_func B C t (@additive_terminal_object
  C Prod t A) R1) (@one_cat_native_cover_left_lift B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 m0 E1) (@one_cat_target_original_cover_lift B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@one_cat_target_cycle_representative B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1)
  (@one_cat_native_cover_left_lift B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R0 R1 m0 E1) (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_precomposition_family_func
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)) (@Transf
  B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src) v
  (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@zero_cone_row_family_source_func B C t (@additive_terminal_object
  C Prod t A) R1) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1)
  (@one_cat_native_cover_left_lift B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R0 R1 m0 E1)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src) (@kernel_precomposition_first_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)))
  (@one_cat_native_cover_left_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 m0 E1)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0 walking_arrow_src)
  (@kernel_precomposition_first_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src)) (@Transf B C
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src) v)) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A
  T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R0 walking_arrow_src) (@kernel_precomposition_first_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2)) (@one_cat_target_middle_boundary_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0
  m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_original_cover_lift_reconstruction B C C1 Prod t A
  T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_target_middle_differential_path B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2)))));

// Original kernel cancellation identifies the covered left cycle with the original class representative.
symbol one_cat_target_left_cycle_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
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
 : τ (@= (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1))) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@one_cat_native_cover_left_cycles B C (@additive_preadditive
  C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)
  (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A
  T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_target_cycle_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2)))
≔ @one_cat_kernel_family_inclusion_reflect_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2) (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@one_cat_target_cycle_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2) (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)) (@Transf B C
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)) (λ v : τ
  (@Transf B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)), (@comp_fapp0 (Functor_cat
  B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1) v
  (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R1) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)) (@one_cat_native_cover_left_lift B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 m0 E1)
  (@one_cat_native_cover_cycles_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2))
  (@one_cat_target_left_lift_path B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
  E1 E2)));

// The original whole ρ gives the right homology preimage.
symbol one_cat_target_homology_preimage [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
 : τ (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_source_homology_func B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2))
≔ (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_cover_transf B C (@additive_preadditive C Prod t A)
  C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2));

// Compose the two derived covers at the actual kernel of H(i).
symbol one_cat_target_cover_composite [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
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
 : τ (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))))
≔ (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@one_cat_target_class_projection B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1 Prod t A T0 P Q
  N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2));

// The whole δρ=θ law reconstructs the covered original left class.
symbol one_cat_target_preimage_reconstruction [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2)) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2) (@one_cat_native_window_connecting_transf B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_target_homology_preimage B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
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
  upper_zero lower_zero Em E0 E1 E2))) (@one_cat_target_cover_composite B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2) (@one_cat_native_window_connecting_transf B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_cover_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P
  Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (λ v : τ (@Transf B C (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)), (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B
  C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) v
  (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@one_cat_native_window_source_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2) (@one_cat_native_window_connecting_transf B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_cover_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_native_window_covered_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_connecting_reconstruction B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_native_window_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_cover_left_cycles B C (@additive_preadditive C Prod t A) C1
  t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)
  (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))) (@Transf B C
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (λ v : τ
  (@Transf B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1))), (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_native_window_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) v)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2) (@one_cat_target_original_cover_lift B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@one_cat_target_cycle_representative B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1 Prod t A T0 P Q N Rm R0 R1
  R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@one_cat_target_left_cycle_path B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C)
  (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_native_window_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_target_cycle_representative B C C1 Prod t A T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_boundary_projection B C C1 Prod t A T0
  P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@Transf
  B C (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (λ v : τ
  (@Transf B C (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero
  lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)),
  (@comp_fapp0 (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2
  mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm
  R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) v (@one_cat_target_boundary_projection B C C1 Prod t A T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_native_window_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_target_cycle_representative B C C1 Prod t A T0 P Q N Rm R0
  R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@one_cat_target_class_projection B C
  C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)) (@eq_sym _ _ _
  (@one_cat_target_class_reconstruction B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2))) (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_target_boundary_cover_func B C C1
  Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_target_class_cover_func B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))
  (@one_cat_native_window_target_homology_func B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@transf_arrow_diagram_func B C (@one_cat_native_window_target_homology_func B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B C C1 Prod t A T0 P Q N
  Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B C C1 Prod t
  A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))) (@one_cat_target_class_projection B C
  C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_target_boundary_projection B C C1 Prod t A T0 P Q N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero
  Em E0 E1 E2)))))))));
