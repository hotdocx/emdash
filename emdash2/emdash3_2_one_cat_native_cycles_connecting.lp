require open emdash.emdash3_2_one_cat_native_connecting_kernel_paths;

// Specialize the original whole annihilation to the original kernel of r.
symbol one_cat_native_theta_kernel_r_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0)) (R0 R1 R2 : τ
  (Functor B (@ZeroArrowCone_cat C t T))) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B
  (@ZeroArrowCone_cat C t T) R1 R2)) (lower_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0
  (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T
  T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T
  R2 walking_arrow_src)))) (E0 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0)) (E1 : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C Add C1
  t T T0 P Q R2))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0))
  (@one_cat_kernel_precomposition_second_transf B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)))) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2))) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@one_cat_kernel_precomposition_second_transf B C Add
  C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))))
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_covered_homology_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1
  lower_zero E1 E2) (@kernel_adjunction_family_inclusion_transf B C Add t T P (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0))
  (@one_cat_kernel_precomposition_second_transf B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0))))) (@zero_arrow_family_zero_transf B C t T T0 (@kernel_adjunction_family_func B C Add t T P
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@one_cat_kernel_precomposition_second_transf B C Add
  C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2))))
≔ @one_cat_native_theta_zero_on_r B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2
  (@kernel_adjunction_family_func B C Add t T P (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0))
  (@one_cat_kernel_precomposition_second_transf B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)))) (@kernel_adjunction_family_inclusion_transf B C Add t T P (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0))
  (@one_cat_kernel_precomposition_second_transf B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)))) (@one_cat_kernel_family_annihilation_path B C Add C1 t T T0 P (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0))
  (@one_cat_kernel_precomposition_second_transf B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0))));

// Descend the original θ through the proved cover of the original r.
symbol one_cat_native_cycles_connecting_transf [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)))) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object
  C Prod t A)) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R1 R2))
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
  R2 walking_arrow_src)))) (E0 : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R2))
 : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R0 R1 m0)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2)))
≔ @one_cat_coimage_cover_descent B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)))
  (@one_cat_kernel_precomposition_cover_omega B C C1 Prod t A T0 P Q N (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0) (@one_cat_short_exact_outgoing_cokernel_zero B C C1 Prod t A T0 P Q
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_row_family_diagram_func B C t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_zero_cone_row_family_transf B C C1 t (@additive_terminal_object C Prod t A) R0) E0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_covered_homology_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E1 E2) (@one_cat_native_theta_kernel_r_zero B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2);

// The first universal descent reconstructs the original whole θ.
symbol one_cat_native_cycles_connecting_reconstruction [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ
  (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)))) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object
  C Prod t A)) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R1 R2))
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
  R2 walking_arrow_src)))) (E0 : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R2))
 : τ (@= (@Transf B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_cycles_connecting_transf B C C1 Prod t A
  T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)))
  (@one_cat_native_covered_homology_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2))
≔ @one_cat_coimage_cover_descent_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod
  t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)))
  (@one_cat_kernel_precomposition_cover_omega B C C1 Prod t A T0 P Q N (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0) (@one_cat_short_exact_outgoing_cokernel_zero B C C1 Prod t A T0 P Q
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_row_family_diagram_func B C t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_zero_cone_row_family_transf B C C1 t (@additive_terminal_object C Prod t A) R0) E0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_covered_homology_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E1 E2) (@one_cat_native_theta_kernel_r_zero B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2);
