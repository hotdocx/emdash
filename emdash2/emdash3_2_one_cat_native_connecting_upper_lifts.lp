require open emdash.emdash3_2_one_cat_kernel_input_boundaries;
require open emdash.emdash3_2_one_cat_native_homology_window_covers;

// The original upper middle-chain law feeds the original composite kernel.
symbol one_cat_native_upper_lift_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
  t T T0 P Q R2)) (Rm : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm
  R0)) (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T
  Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t
  T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (Em : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm))
 : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) (@diagram_family_transf B
  WalkingArrow_cat C (@precomposed_diagram_family_func B C (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@zero_cone_row_family_vertex_map B C t T
  Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t
  T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt)) (λ h : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) h
  (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src))) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T
  R0)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R1) (@zero_cone_row_family_vertex_map B C t T R0 R1
  m0 walking_arrow_src)) (@one_cat_zero_cone_row_outgoing_square_path B C C1 t T R0 R1 m0)) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R1) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt)) (λ h : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R1) h)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T
  Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t
  T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) upper_zero)
  (@one_cat_zero_family_postcompose_path B C C1 t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T
  R1)))));

// Lift the original upper middle differential into the existing L.
symbol one_cat_native_upper_lift_transf [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
  t T T0 P Q R2)) (Rm : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm
  R0)) (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T
  Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t
  T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (Em : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm))
 : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)))
≔ @one_cat_kernel_family_lift B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@precomposed_diagram_family_func B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src) (@one_cat_native_upper_lift_zero B C
  Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em);

// The original first projection reconstructs the entire upper middle differential.
symbol one_cat_native_upper_lift_reconstruction [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ
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
 : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm
  mm upper_zero Em)) (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src))
≔ @one_cat_kernel_family_lift_ambient_reconstruction B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C t
  T Rm walking_arrow_src) (@precomposed_diagram_family_func B C (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src)
  (@one_cat_native_upper_lift_zero B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero
  Em);

// The original r sends this lift to the original right boundary after the upper row map.
symbol one_cat_native_upper_lift_boundary_path [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ
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
 : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)))
  (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0))
  (@one_cat_kernel_precomposition_second_transf B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_tgt) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@kernel_adjunction_family_boundary_transf B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q Rm R0 R1 mm m0 upper_zero Em))
  (@zero_cone_row_family_outgoing B C t T Rm)))
≔ @one_cat_kernel_family_inclusion_reflect_path B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@one_cat_kernel_precomposition_second_transf B C Add
  C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_tgt) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@kernel_adjunction_family_boundary_transf B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q Rm R0 R1 mm m0 upper_zero Em))
  (@zero_cone_row_family_outgoing B C t T Rm)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@one_cat_kernel_precomposition_second_transf B C Add
  C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt)) (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)) (λ h : τ (@Transf B C
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) h (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0
  E1 E2 Rm mm upper_zero Em))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@one_cat_kernel_precomposition_second_transf B C Add
  C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)))
  (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R0) (@kernel_precomposition_first_transf B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))) (@one_cat_kernel_precomposition_square_path B C Add C1 t
  T T0 P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B
  C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C
  t T R0 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R0) (@kernel_precomposition_first_transf B C
  Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)) (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt)) (λ h : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R0) h)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm
  mm upper_zero Em)) (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src)
  (@one_cat_native_upper_lift_reconstruction B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@one_cat_zero_cone_row_outgoing_square_path B C C1 t T Rm R0
  mm)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_tgt)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)) (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt)) (λ h : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_tgt)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) h
  (@zero_cone_row_family_outgoing B C t T Rm))) (@zero_cone_row_family_vertex_map B C t T Rm R0 mm
  walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_tgt) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
  (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R0 R1
  m0)) (@kernel_adjunction_family_boundary_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q Rm R0 R1 mm m0 upper_zero Em))) (@eq_sym _ _ _
  (@one_cat_kernel_input_boundary_reconstruction B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C
  t T Rm walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_tgt) (@one_cat_zero_cone_right_column_zero_path
  B C Add C1 t T T0 P Q Rm R0 R1 mm m0 upper_zero Em)))) (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_tgt) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
  (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R0 R1
  m0)) (@kernel_adjunction_family_boundary_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q Rm R0 R1 mm m0 upper_zero Em))
  (@zero_cone_row_family_outgoing B C t T Rm)))))))));

// The original incoming-row cancellation makes the covered left lift zero.
symbol one_cat_native_upper_lift_left_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
  t T T0 P Q R2)) (Rm : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm
  R0)) (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T
  Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t
  T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (Em : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm))
 : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_source_func B C t T R1)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1)
  (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1) (@one_cat_native_upper_lift_transf B C
  Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em)) (@zero_arrow_family_zero_transf B C t
  T T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_source_func B C t T
  R1)))
≔ @one_cat_short_exact_family_incoming_reflect_path B C Add C1 t T T0 P Q (@zero_cone_row_family_source_func B C t
  T R1) (@zero_cone_row_family_diagram_func B C t T R1) (@one_cat_zero_cone_row_family_transf B C C1 t T R1) E1
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1)
  (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1) (@one_cat_native_upper_lift_transf B C
  Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em)) (@zero_arrow_family_zero_transf B C t
  T T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_source_func B C t T
  R1)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R1) (@one_cat_native_cover_left_lift B C
  Add C1 t T T0 P Q R0 R1 m0 E1) (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1
  lower_zero E0 E1 E2 Rm mm upper_zero Em)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (λ h : τ (@Transf B C (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) h
  (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1
  t T R1) (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C
  t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
  (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0))) (@one_cat_native_cover_left_reconstruction B C Add C1 t T T0 P Q R0 R1 m0 E1)) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C
  t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
  (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)) (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (λ h : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) h)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm
  mm upper_zero Em)) (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src)
  (@one_cat_native_upper_lift_reconstruction B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em)) (@eq_trans _ _ _ _ upper_zero (@eq_sym _ _ _ (@one_cat_zero_family_postcompose_path B C C1 t T
  T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_source_func B C t T
  R1) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C
  C1 t T R1))))))));

// Original kernel cancellation makes the whole covered left cycle zero.
symbol one_cat_native_upper_lift_cycles_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
  t T T0 P Q R2)) (Rm : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm
  R0)) (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T
  Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t
  T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (Em : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm))
 : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)))
  (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)
  (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1))))
≔ @one_cat_kernel_family_inclusion_reflect_path B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P
  Q R0 R1 R2 m0 m1 lower_zero E1 E2) (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1
  lower_zero E0 E1 E2 Rm mm upper_zero Em)) (@zero_arrow_family_zero_transf B C t T T0
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_source_func B C t T R1)
  (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2
  m1)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)
  (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1)) (@Transf
  B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_source_func B C t T
  R1)) (λ h : τ (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func
  B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1)), (@comp_fapp0
  (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_source_func B C t T R1) h (@one_cat_native_upper_lift_transf B C Add C1 t
  T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@zero_cone_row_family_source_func B C t T R1) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P
  Q R0 R1 R2 m0 m1 lower_zero E1 E2)) (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1)
  (@one_cat_native_cover_cycles_reconstruction B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)) (@eq_trans
  _ _ _ _ (@one_cat_native_upper_lift_left_zero B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm
  mm upper_zero Em) (@eq_sym _ _ _ (@one_cat_zero_family_postcompose_path B C C1 t T T0
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_source_func B C t T R1)
  (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2
  m1)))))));

// The original whole θ kills this lifted upper differential.
symbol one_cat_native_upper_lift_theta_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
  t T T0 P Q R2)) (Rm : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm
  R0)) (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T
  Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t
  T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (Em : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm))
 : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_covered_homology_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1
  lower_zero E1 E2) (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1
  E2 Rm mm upper_zero Em)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T
  Rm walking_arrow_src) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B
  C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add
  C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2
  m1)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)) (@homology_adjunction_family_projection_transf B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)
  (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1))) (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2))) (λ h : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1))), (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)) (@homology_adjunction_family_projection_transf B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) h)) (@comp_fapp0
  (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)
  (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1))) (@one_cat_native_upper_lift_cycles_zero B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1
  E2 Rm mm upper_zero Em)) (@one_cat_zero_family_postcompose_path B C C1 t T T0 (@zero_cone_row_family_vertex_func
  B C t T Rm walking_arrow_src) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)))));
