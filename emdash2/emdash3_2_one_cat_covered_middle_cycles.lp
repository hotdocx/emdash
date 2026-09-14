require open emdash.emdash3_2_one_cat_native_connecting_kernel_paths;

// Original incoming cancellation detects zero from the covered middle differential.
symbol one_cat_native_cover_left_middle_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
  t T T0 P Q R2)) (V : τ (Functor B C)) (s : τ (@Transf B C V (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)))) (e : τ (@= (@Transf B C V
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) V
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@comp_fapp0
  (Functor_cat B C) V (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@kernel_precomposition_first_transf
  B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) s))
  (@zero_arrow_family_zero_transf B C t T T0 V (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src))))
 : τ (@= (@Transf B C V (@zero_cone_row_family_source_func B C t T R1)) (@comp_fapp0 (Functor_cat B C) V
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_source_func B C t T R1) (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q
  R0 R1 m0 E1) s) (@zero_arrow_family_zero_transf B C t T T0 V (@zero_cone_row_family_source_func B C t T R1)))
≔ @one_cat_short_exact_family_incoming_reflect_path B C Add C1 t T T0 P Q (@zero_cone_row_family_source_func B C t
  T R1) (@zero_cone_row_family_diagram_func B C t T R1) (@one_cat_zero_cone_row_family_transf B C C1 t T R1) E1 V
  (@comp_fapp0 (Functor_cat B C) V (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1)
  (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1) s) (@zero_arrow_family_zero_transf B C t T
  T0 V (@zero_cone_row_family_source_func B C t T R1)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) V
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R1) (@one_cat_native_cover_left_lift B C
  Add C1 t T T0 P Q R0 R1 m0 E1) s) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_precomposition_family_func B
  C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@Transf B C V
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (λ h : τ (@Transf B C
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) V
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) h s)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R1) (@one_cat_native_cover_left_lift B C
  Add C1 t T T0 P Q R0 R1 m0 E1)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@kernel_precomposition_first_transf B C
  Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)))
  (@one_cat_native_cover_left_reconstruction B C Add C1 t T T0 P Q R0 R1 m0 E1)) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@comp_assoc (Functor_cat B C) V (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@kernel_precomposition_first_transf B C
  Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) s))
  (@eq_trans _ _ _ _ e (@eq_sym _ _ _ (@one_cat_zero_family_postcompose_path B C C1 t T T0 V
  (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t T R1)))))));

// Original kernel cancellation makes the corresponding whole left cycle zero.
symbol one_cat_native_cover_cycles_middle_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ
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
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (V : τ (Functor B C)) (s : τ (@Transf B C V
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)))) (e : τ (@= (@Transf B C V (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src))
  (@comp_fapp0 (Functor_cat B C) V (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1
  m0 walking_arrow_src) (@comp_fapp0 (Functor_cat B C) V (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) s)) (@zero_arrow_family_zero_transf B C t T T0 V (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src))))
 : τ (@= (@Transf B C V (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t
  T R1 R2 m1))) (@comp_fapp0 (Functor_cat B C) V (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P
  Q R0 R1 R2 m0 m1 lower_zero E1 E2) s) (@zero_arrow_family_zero_transf B C t T T0 V
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))))
≔ @one_cat_kernel_family_inclusion_reflect_path B C Add C1 t T T0 P V (@zero_cone_left_column_outgoing_func B C t
  T R1 R2 m1) (@comp_fapp0 (Functor_cat B C) V (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P
  Q R0 R1 R2 m0 m1 lower_zero E1 E2) s) (@zero_arrow_family_zero_transf B C t T T0 V
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)))
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) V (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_source_func B C t T R1)
  (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2
  m1)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2) s) (@eq_trans _ _
  _ _ (@eq_ap (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B
  C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1)) (@Transf B C V
  (@zero_cone_row_family_source_func B C t T R1)) (λ h : τ (@Transf B C (@kernel_precomposition_family_func B C
  Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@zero_cone_row_family_source_func B C t T R1)), (@comp_fapp0 (Functor_cat B C) V
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_source_func B C t T R1) h s)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@zero_cone_row_family_source_func B C t T R1) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P
  Q R0 R1 R2 m0 m1 lower_zero E1 E2)) (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1)
  (@one_cat_native_cover_cycles_reconstruction B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)) (@eq_trans
  _ _ _ _ (@one_cat_native_cover_left_middle_zero B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 V
  s e) (@eq_sym _ _ _ (@one_cat_zero_family_postcompose_path B C C1 t T T0 V (@kernel_adjunction_family_func B C
  Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_source_func B C t T
  R1) (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1
  R2 m1)))))));

// The original θ kills every covered middle cycle.
symbol one_cat_native_theta_middle_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
  t T T0 P Q R2)) (V : τ (Functor B C)) (s : τ (@Transf B C V (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)))) (e : τ (@= (@Transf B C V
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) V
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@comp_fapp0
  (Functor_cat B C) V (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@kernel_precomposition_first_transf
  B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) s))
  (@zero_arrow_family_zero_transf B C t T T0 V (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src))))
 : τ (@= (@Transf B C V (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B
  C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add
  C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))) (@comp_fapp0 (Functor_cat B C) V
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_covered_homology_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1
  lower_zero E1 E2) s) (@zero_arrow_family_zero_transf B C t T T0 V (@homology_adjunction_family_func B C Add t T
  T0 P Q (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) V (@kernel_precomposition_family_func B C Add t
  T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C
  t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q R0 R1 R2 m0 m1
  lower_zero E1 E2) s)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C V (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))) (@Transf B C V (@homology_adjunction_family_func B C
  Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1
  R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))) (λ h : τ
  (@Transf B C V (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2
  m1))), (@comp_fapp0 (Functor_cat B C) V (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)) h)) (@comp_fapp0 (Functor_cat B C) V (@kernel_precomposition_family_func B C
  Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2) s)
  (@zero_arrow_family_zero_transf B C t T T0 V (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))) (@one_cat_native_cover_cycles_middle_zero B C
  Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 V s e)) (@one_cat_zero_family_postcompose_path B C C1 t T
  T0 V (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)) (@homology_adjunction_family_projection_transf B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2)))));
