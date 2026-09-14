require open emdash.emdash3_2_one_cat_row_homology_zero_pairs;
require open emdash.emdash3_2_one_cat_native_connecting;

// Original row and kernel reconstruction identify the induced covered cycle with the original middle boundary.
symbol one_cat_native_incoming_cycles_boundary_path [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0)) (R0 R1
  R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ
  (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (lower_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
  m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ (@OneCatZeroConeShortExactFamily B C
  Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (Rm : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm
  : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0)) (upper_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1
  m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (Em : τ (@OneCatZeroConeShortExactFamily B C
  Add C1 t T T0 P Q Rm))
 : τ (@= (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T
  R1 R2 m1))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  Add C1 t T T0 P Q (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_incoming_diagram_map
  B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E1 E2)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add
  t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B
  C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1)) (@kernel_adjunction_family_boundary_transf B C Add t T P (@zero_cone_row_family_vertex_func B C
  t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0))))
≔ @one_cat_kernel_family_inclusion_reflect_path B C Add C1 t T T0 P (@kernel_precomposition_family_func B C Add t
  T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C
  t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_middle_column_outgoing_func B C t T
  R1 R2 m1) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  Add C1 t T T0 P Q (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_incoming_diagram_map
  B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E1 E2)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add
  t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B
  C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1)) (@kernel_adjunction_family_boundary_transf B C Add t T P (@zero_cone_row_family_vertex_func B C
  t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  Add C1 t T T0 P Q (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_incoming_diagram_map
  B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B
  C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T
  R1 walking_arrow_src)) (@Transf B C (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) v (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)))
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  Add C1 t T T0 P Q (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_incoming_diagram_map
  B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t T R1) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)))
  (@one_cat_row_triple_incoming_cycle_projection_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1
  E2)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_precomposition_family_func B C
  Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t T R1) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P
  Q R0 R1 R2 m0 m1 lower_zero E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_precomposition_family_func
  B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@zero_cone_row_family_source_func B C t T R1)) (@Transf B C (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1)),
  (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1
  t T R1) v)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_source_func B C t T R1)
  (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2
  m1)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2))
  (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1) (@one_cat_native_cover_cycles_reconstruction
  B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)) (@eq_trans _ _ _ _
  (@one_cat_native_cover_left_reconstruction B C Add C1 t T T0 P Q R0 R1 m0 E1) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
  B C t T R1 walking_arrow_src)) (@Transf B C (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C
  t T R1 walking_arrow_src) v (@kernel_precomposition_first_transf B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)))) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0
  walking_arrow_src) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T
  R1 R2 m1)) (@kernel_adjunction_family_boundary_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))) (@eq_sym _ _ _
  (@one_cat_kernel_input_boundary_reconstruction B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) lower_zero))) (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@kernel_adjunction_family_func B C
  Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B
  C t T R1 walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_boundary_transf B C
  Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) (@kernel_precomposition_first_transf B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))))))))));

// The original middle quotient kills the incoming image of the existing θ.
symbol one_cat_native_incoming_homology_theta_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0)) (R0 R1
  R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ
  (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (lower_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
  m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ (@OneCatZeroConeShortExactFamily B C
  Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (Rm : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm
  : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0)) (upper_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1
  m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (Em : τ (@OneCatZeroConeShortExactFamily B C
  Add C1 t T T0 P Q Rm))
 : τ (@= (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))) (@comp_fapp0
  (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@one_cat_row_triple_incoming_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_native_covered_homology_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2))
  (@zero_arrow_family_zero_transf B C t T T0 (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@one_cat_row_triple_incoming_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q R0 R1 R2 m0 m1
  lower_zero E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)))
  (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))) (λ v : τ (@Transf B C
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))), (@comp_fapp0
  (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2
  m1)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) v
  (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2))) (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1
  R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@one_cat_row_triple_incoming_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2))) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T
  T0 P Q (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) (@homology_adjunction_family_projection_transf B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@kernel_adjunction_family_map_transf B C Add C1 t T T0 P Q (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@one_cat_row_triple_incoming_homology_projection_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0
  E1 E2)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_precomposition_family_func B C
  Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@kernel_adjunction_family_map_transf B C Add C1 t T T0 P Q (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t
  T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing
  B C t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T
  R1 R2 m1))) (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B
  C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))) (λ v :
  τ (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1
  R2 m1))), (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T
  T0 P Q (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) (@homology_adjunction_family_projection_transf B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) v))
  (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  Add C1 t T T0 P Q (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_incoming_diagram_map
  B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E1 E2)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add
  t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B
  C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1)) (@kernel_adjunction_family_boundary_transf B C Add t T P (@zero_cone_row_family_vertex_func B C
  t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0))) (@one_cat_native_incoming_cycles_boundary_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2 Rm mm upper_zero Em)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@kernel_adjunction_family_func B C
  Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C
  Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) (@homology_adjunction_family_projection_transf B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@kernel_adjunction_family_boundary_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t
  T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))) (@Transf B C
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))) (λ v : τ (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@homology_adjunction_family_func B C Add t T
  T0 P Q (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))), (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C
  Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@homology_adjunction_family_func B C Add t T
  T0 P Q (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) v (@kernel_precomposition_first_transf B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)))) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T
  T0 P Q (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) (@homology_adjunction_family_projection_transf B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@kernel_adjunction_family_boundary_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)))
  (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)))
  (@one_cat_cokernel_family_annihilation_path B C Add C1 t T T0 Q (@kernel_adjunction_family_boundary_diagram_func
  B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)))) (@one_cat_zero_family_precompose_path B C C1 t T T0
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@homology_adjunction_family_func B C
  Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) (@kernel_precomposition_first_transf B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)))))))));

// Original categorical cover cancellation proves H(i)∘δ=0 at the retained homology objects.
symbol one_cat_native_incoming_connecting_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  A) T0 P Q R2)) (Rm : τ (Functor B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)))) (mm : τ
  (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) Rm R0)) (upper_zero : τ (@= (@Transf
  B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src))
  (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) Rm R0 mm
  walking_arrow_src)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)))) (Em : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q Rm))
 : τ (@= (@Transf B C (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero
  Em)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1
  R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2
  m0 m1 lower_zero))) (@comp_fapp0 (Functor_cat B C) (@homology_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero
  Em)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero))
  (@one_cat_row_triple_incoming_homology_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_native_connecting_transf B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero
  Em)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero))))
≔ @one_cat_coimage_cover_reflect_path B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero
  Em)) (@one_cat_homology_cover_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0))) (@one_cat_homology_cover_omega B C C1 Prod t A T0 P Q N
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_short_exact_outgoing_cokernel_zero B C C1 Prod t A T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_row_family_diagram_func B C t (@additive_terminal_object
  C Prod t A) R0) (@one_cat_zero_cone_row_family_transf B C C1 t (@additive_terminal_object C Prod t A) R0) E0)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@comp_fapp0 (Functor_cat B C)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1
  R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2
  m0 m1 lower_zero)) (@one_cat_row_triple_incoming_homology_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_native_connecting_transf B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero
  Em)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero))) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@comp_assoc (Functor_cat B C) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1
  R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2
  m0 m1 lower_zero)) (@one_cat_row_triple_incoming_homology_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_native_connecting_transf B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero
  Em) (@one_cat_homology_cover_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2))) (@Transf B C (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero))) (λ v : τ (@Transf B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2))), (@comp_fapp0 (Functor_cat B C)
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero))
  (@one_cat_row_triple_incoming_homology_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2) v)) (@comp_fapp0 (Functor_cat
  B C) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2)) (@one_cat_native_connecting_transf B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em) (@one_cat_homology_cover_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero
  Em) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)))
  (@one_cat_native_covered_homology_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2) (@one_cat_native_connecting_reconstruction B C C1 Prod t A
  T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em)) (@eq_trans _ _ _ _
  (@one_cat_native_incoming_homology_theta_zero B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em) (@eq_sym _
  _ _ (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@one_cat_homology_cover_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)))))));
