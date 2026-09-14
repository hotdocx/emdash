require open emdash.emdash3_2_one_cat_row_homology_maps;
require open emdash.emdash3_2_one_cat_image_kernel_comparison;

// The original zero row and kernel cancellation make the two induced cycle maps compose to zero.
symbol one_cat_row_triple_cycle_maps_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R1 R2
  m1))) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_map_transf B C Add C1
  t T T0 P Q (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_outgoing_diagram_map B C Add
  C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@kernel_adjunction_family_map_transf B C Add C1 t T T0
  P Q (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t
  T R1 R2 m1) (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0
  E1 E2))) (@zero_arrow_family_zero_transf B C t T T0 (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1))))
≔ @one_cat_kernel_family_inclusion_reflect_path B C Add C1 t T T0 P (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_right_column_outgoing_func B C t T R1 R2
  m1) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_map_transf B C Add C1
  t T T0 P Q (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_outgoing_diagram_map B C Add
  C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@kernel_adjunction_family_map_transf B C Add C1 t T T0
  P Q (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t
  T R1 R2 m1) (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0
  E1 E2))) (@zero_arrow_family_zero_transf B C t T T0 (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C)
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1))
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf B C
  Add t T P (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_map_transf
  B C Add C1 t T T0 P Q (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_outgoing_diagram_map B C Add
  C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@kernel_adjunction_family_map_transf B C Add C1 t T T0
  P Q (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t
  T R1 R2 m1) (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0
  E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt)) (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt)) (λ v : τ (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt) v (@kernel_adjunction_family_map_transf B C Add C1 t T T0 P Q
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t T R1
  R2 m1) (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1
  E2)))) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_map_transf B C Add C1
  t T T0 P Q (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_outgoing_diagram_map B C Add
  C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R1) (@kernel_adjunction_family_inclusion_transf B C
  Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)))
  (@one_cat_row_triple_outgoing_cycle_projection_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1
  E2)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C Add t
  T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R1) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  Add C1 t T T0 P Q (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_incoming_diagram_map
  B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@Transf B C (@kernel_adjunction_family_func B
  C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T
  R1 walking_arrow_tgt)) (λ v : τ (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R1) v)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B
  C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T
  P (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
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
  E2)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_source_func B C t T R1)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R1) (@one_cat_zero_cone_row_family_incoming B C C1 t
  T R1) (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1
  R2 m1))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_source_func B C t T R1)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (@Transf B C (@kernel_adjunction_family_func B
  C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T
  R1 walking_arrow_tgt)) (λ v : τ (@Transf B C (@zero_cone_row_family_source_func B C t T R1)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
  v (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2
  m1)))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R1)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R1) (@one_cat_zero_cone_row_family_incoming B C C1 t
  T R1)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_source_func B C t T R1)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (@one_cat_zero_family_chain_path B C C1 t T T0
  (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_diagram_func B C t T R1)
  (@one_cat_zero_cone_row_family_transf B C C1 t T R1))) (@eq_trans _ _ _ _ (@one_cat_zero_family_precompose_path
  B C C1 t T T0 (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2
  m1)) (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))) (@eq_sym _ _ _ (@one_cat_zero_family_postcompose_path
  B C C1 t T T0 (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2
  m1)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf B C
  Add t T P (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)))))))))));

// The original quotient cancels to give the whole zero composite H(p)∘H(i).
symbol one_cat_row_triple_homology_maps_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
 : τ (@= (@Transf B C (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C
  t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1
  t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T
  R1 R2 m1) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0)))
  (@comp_fapp0 (Functor_cat B C) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@one_cat_row_triple_outgoing_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_row_triple_incoming_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@zero_arrow_family_zero_transf B C t T T0 (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))))
≔ @one_cat_homology_projection_reflect_path B C Add C1 t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T
  R1 R2 m1) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@comp_fapp0 (Functor_cat B C) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@one_cat_row_triple_outgoing_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_row_triple_incoming_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@zero_arrow_family_zero_transf B C t T T0 (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@one_cat_row_triple_outgoing_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_row_triple_incoming_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C
  Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T
  T0 P Q (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))) (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T
  R1 R2 m1) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))) (λ v : τ
  (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2
  m1)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))), (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1
  R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@one_cat_row_triple_outgoing_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2) v))
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
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
  E1 E2)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T
  T0 P Q (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T
  R1 R2 m1) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@one_cat_row_triple_outgoing_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@kernel_adjunction_family_map_transf B C Add C1 t T T0 P Q (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T
  T0 P Q (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0)))
  (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2
  m1)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))) (λ v : τ (@Transf B
  C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))), (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1
  R2 m1)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1
  R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) v
  (@kernel_adjunction_family_map_transf B C Add C1 t T T0 P Q (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))))
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T
  T0 P Q (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T
  R1 R2 m1) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@one_cat_row_triple_outgoing_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))) (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R1
  R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@kernel_adjunction_family_map_transf B C Add C1 t T T0 P Q (@zero_cone_middle_column_outgoing_func
  B C t T R1 R2 m1) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@one_cat_row_triple_outgoing_homology_projection_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0
  E1 E2)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C Add
  t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T
  R1 R2 m1) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@kernel_adjunction_family_map_transf B C Add C1 t T T0 P Q (@zero_cone_middle_column_outgoing_func
  B C t T R1 R2 m1) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@kernel_adjunction_family_map_transf B C Add C1 t T T0 P Q (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1))) (@Transf B C (@kernel_adjunction_family_func B C Add
  t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0
  P Q (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C
  t T R1 R2 m1) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))) (λ v
  : τ (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1
  R2 m1)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R1 R2
  m1))), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T
  R1 R2 m1) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) v)) (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1
  R2 m1)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1
  R2 m1)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C Add C1 t T T0 P Q (@zero_cone_middle_column_outgoing_func
  B C t T R1 R2 m1) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@kernel_adjunction_family_map_transf B C Add C1 t T T0 P Q (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@zero_arrow_family_zero_transf B C t T T0 (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1))) (@one_cat_row_triple_cycle_maps_zero B C Add C1
  t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@eq_trans _ _ _ _ (@one_cat_zero_family_postcompose_path B C C1
  t T T0 (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))) (@eq_sym _ _ _
  (@one_cat_zero_family_precompose_path B C C1 t T T0 (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)))))))))));

// The proved zero composite forms the native H(i),H(p) input before selecting its comparison.
symbol one_cat_row_triple_homology_zero_input [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
 : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2)))
  (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@one_cat_row_triple_outgoing_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
≔ @one_cat_kernel_family_input B C C1 t T T0 (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@one_cat_row_triple_outgoing_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_row_triple_incoming_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_row_triple_homology_maps_zero B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2);

// This is the existing actual Im(H(i))⇒K(H(p)) comparison; invertibility is still to be proved.
symbol one_cat_row_triple_homology_exact_comparison [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ
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
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (N : τ (@OneCatAdjunctionNormality C Add C1 t T T0 P
  Q))
 : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C Add t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@one_cat_row_triple_outgoing_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_row_triple_homology_zero_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@kernel_adjunction_family_func B C Add t T P (@transf_arrow_diagram_func B C (@homology_adjunction_family_func
  B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T
  R1 R2 m1) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@one_cat_row_triple_outgoing_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))))
≔ @one_cat_image_to_kernel_transf B C Add C1 t T T0 P Q (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@one_cat_row_triple_outgoing_homology_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_row_triple_homology_zero_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2) N;
