require open emdash.emdash3_2_one_cat_row_homology_zero_pairs;
require open emdash.emdash3_2_one_cat_covered_middle_cycles;
require open emdash.emdash3_2_one_cat_native_connecting;

// The original middle kernel inclusion satisfies the zero needed by the existing L.
symbol one_cat_native_middle_cycle_cover_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func
  B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B
  C) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R0 R1
  m0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T
  R1 walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C (@precomposed_diagram_family_func B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0))) (@zero_arrow_family_zero_transf B C t T T0
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0))
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (@Transf B C (@kernel_adjunction_family_func B
  C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func
  B C t T R1 walking_arrow_tgt)) (λ v : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)), (@comp_fapp0 (Functor_cat
  B C) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R0 R1
  m0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T
  R1 walking_arrow_tgt) v (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)))) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T
  R0)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R1) (@zero_cone_row_family_vertex_map B C t T R0 R1
  m0 walking_arrow_src)) (@one_cat_zero_cone_row_outgoing_square_path B C C1 t T R0 R1 m0)) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R1)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T
  R0 R1 m0)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt)) (λ v : τ (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R1) v)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B
  C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func
  B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T
  R0 R1 m0))) (@zero_arrow_family_zero_transf B C t T T0 (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (@one_cat_kernel_family_annihilation_path B C Add C1 t T T0 P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0))) (@one_cat_zero_family_postcompose_path B C C1
  t T T0 (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R0 R1
  m0)) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T
  R1 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R1)))));

// Lift the whole original middle cycle inclusion into the same original L.
symbol one_cat_native_middle_cycle_cover_lift [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
 : τ (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C
  t T R0 R1 m0)) (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)))
≔ @one_cat_kernel_family_lift B C Add C1 t T T0 P (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@precomposed_diagram_family_func B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@one_cat_native_middle_cycle_cover_zero
  B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em);

// The first projection reconstructs the original middle kernel inclusion.
symbol one_cat_native_middle_cycle_cover_reconstruction [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 :
  τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
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
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func
  B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)) (@comp_fapp0 (Functor_cat B
  C) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R0 R1
  m0)) (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@kernel_precomposition_first_transf B
  C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@one_cat_native_middle_cycle_cover_lift B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em)) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)))
≔ @one_cat_kernel_family_lift_ambient_reconstruction B C Add C1 t T T0 P (@kernel_adjunction_family_func B C Add t
  T P (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@precomposed_diagram_family_func B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@one_cat_native_middle_cycle_cover_zero
  B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em);

// The original r reconstructs the original induced right cycle map.
symbol one_cat_native_middle_cycle_cover_projection [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ
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
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func
  B C t T R0 R1 m0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0))) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@one_cat_kernel_precomposition_second_transf B C Add
  C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@one_cat_native_middle_cycle_cover_lift B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em)) (@kernel_adjunction_family_map_transf B C Add C1 t T T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@one_cat_row_triple_outgoing_diagram_map B C Add C1 t T T0 P Q Rm R0 R1 mm m0 upper_zero Em E0
  E1)))
≔ @one_cat_kernel_family_inclusion_reflect_path B C Add C1 t T T0 P (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@one_cat_kernel_precomposition_second_transf B C Add
  C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@one_cat_native_middle_cycle_cover_lift B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em)) (@kernel_adjunction_family_map_transf B C Add C1 t T T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@one_cat_row_triple_outgoing_diagram_map B C Add C1 t T T0 P Q Rm R0 R1 mm m0 upper_zero Em E0
  E1)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@one_cat_kernel_precomposition_second_transf B C Add
  C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@one_cat_native_middle_cycle_cover_lift B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt)) (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt)) (λ v : τ (@Transf B C (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@kernel_precomposition_family_func B C Add t T
  P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) v (@one_cat_native_middle_cycle_cover_lift B C Add C1 t T T0 P Q R0 R1 R2 m0 m1
  lower_zero E0 E1 E2 Rm mm upper_zero Em))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B
  C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0))
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf B C
  Add t T P (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0))
  (@one_cat_kernel_precomposition_second_transf B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R0) (@kernel_precomposition_first_transf B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))) (@one_cat_kernel_precomposition_square_path B C Add C1 t
  T T0 P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B
  C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B
  C t T R0 R1 m0)) (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C
  t T R0 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R0) (@kernel_precomposition_first_transf B C
  Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@one_cat_native_middle_cycle_cover_lift B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src)) (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt)) (λ v : τ (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R0) v)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B
  C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@kernel_precomposition_family_func
  B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@kernel_precomposition_first_transf B C Add t
  T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C
  t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@one_cat_native_middle_cycle_cover_lift B C
  Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em))
  (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T
  R0 R1 m0)) (@one_cat_native_middle_cycle_cover_reconstruction B C Add C1 t T T0 P Q R0 R1 R2 m0 m1
  lower_zero E0 E1 E2 Rm mm upper_zero Em)) (@eq_sym _ _ _
  (@one_cat_row_triple_outgoing_cycle_projection_path B C Add C1 t T T0 P Q Rm R0 R1 mm m0 upper_zero Em E0
  E1))))));

// The original θ kills this covered middle cycle.
symbol one_cat_native_middle_cycle_theta_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func
  B C t T R0 R1 m0)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t
  T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t
  T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add
  t T P (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@kernel_precomposition_family_func B C
  Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_covered_homology_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1
  lower_zero E1 E2) (@one_cat_native_middle_cycle_cover_lift B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2 Rm mm upper_zero Em)) (@zero_arrow_family_zero_transf B C t T T0 (@kernel_adjunction_family_func B C
  Add t T P (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@homology_adjunction_family_func B C
  Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1
  R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))))
≔ @one_cat_native_theta_middle_zero B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0))
  (@one_cat_native_middle_cycle_cover_lift B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src)) (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) v)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0))
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@kernel_precomposition_first_transf B
  C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@one_cat_native_middle_cycle_cover_lift B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em)) (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0))
  (@one_cat_native_middle_cycle_cover_reconstruction B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1
  E2 Rm mm upper_zero Em)) (@one_cat_kernel_family_annihilation_path B C Add C1 t T T0 P
  (@zero_cone_middle_column_outgoing_func B C t T R0 R1 m0)));

// The first descent γ kills the actual induced right cycle map.
symbol one_cat_native_cycles_connecting_projection_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2))) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2)) (@one_cat_native_cycles_connecting_transf B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_row_triple_outgoing_diagram_map B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero
  Em E0 E1))) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2))))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0))) (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2))) (λ v : τ (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))), (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2)) (@one_cat_native_cycles_connecting_transf B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) v))
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_row_triple_outgoing_diagram_map B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero
  Em E0 E1)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@kernel_precomposition_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@one_cat_native_middle_cycle_cover_lift B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em)) (@eq_sym
  _ _ _ (@one_cat_native_middle_cycle_cover_projection B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em)))
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@kernel_precomposition_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2)) (@one_cat_native_cycles_connecting_transf B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod
  t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@one_cat_native_middle_cycle_cover_lift B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2))) (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2))) (λ v : τ (@Transf B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2))), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) v (@one_cat_native_middle_cycle_cover_lift B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2 Rm mm upper_zero Em))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2)) (@one_cat_native_cycles_connecting_transf B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod
  t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)))
  (@one_cat_native_covered_homology_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2) (@one_cat_native_cycles_connecting_reconstruction B C C1
  Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_native_middle_cycle_theta_zero B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2 Rm mm upper_zero Em))));

// Original whole quotient cancellation proves δ∘H(p)=0 at the retained homology objects.
symbol one_cat_native_connecting_projection_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
  τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
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
  (@additive_terminal_object C Prod t A) Rm walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 Rm R0 R1 mm m0 upper_zero)) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2))) (@comp_fapp0 (Functor_cat B C)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 Rm R0 R1 mm m0
  upper_zero)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero
  Em)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_connecting_transf B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em) (@one_cat_row_triple_outgoing_homology_map B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero
  Em E0 E1)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 Rm R0 R1 mm m0
  upper_zero)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2))))
≔ @one_cat_homology_projection_reflect_path B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0
  R1 m0) (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 Rm R0 R1
  mm m0 upper_zero) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2)) (@comp_fapp0 (Functor_cat B C) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 Rm R0 R1 mm m0 upper_zero)) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2)) (@one_cat_native_connecting_transf B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm
  upper_zero Em) (@one_cat_row_triple_outgoing_homology_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em E0 E1))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 Rm R0 R1 mm m0
  upper_zero)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 Rm R0 R1 mm m0
  upper_zero)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero
  Em)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_connecting_transf B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em) (@one_cat_row_triple_outgoing_homology_map B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero
  Em E0 E1) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 Rm R0 R1 mm m0 upper_zero)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em))) (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2))) (λ v : τ (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em))), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
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
  upper_zero Em) v)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 Rm R0 R1 mm m0 upper_zero)) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em)) (@one_cat_row_triple_outgoing_homology_map B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero
  Em E0 E1) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 Rm R0 R1 mm m0 upper_zero))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em)) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em E0 E1)))
  (@one_cat_row_triple_outgoing_homology_projection_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em E0 E1)) (@eq_trans _ _ _ _
  (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero
  Em)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_connecting_transf B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em E0 E1))) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2))) (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2))) (λ v : τ (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2))), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) v (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero Em E0 E1)))) (@comp_fapp0 (Functor_cat B
  C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
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
  upper_zero Em) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q Rm R0 R1 mm m0 upper_zero
  Em))) (@one_cat_native_cycles_connecting_transf B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_native_connecting_quotient_reconstruction B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2
  Rm mm upper_zero Em)) (@eq_trans _ _ _ _ (@one_cat_native_cycles_connecting_projection_zero B C C1 Prod t
  A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero Em) (@eq_sym _ _ _
  (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 Rm R0 R1 mm m0
  upper_zero)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2)) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) Rm walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 Rm R0 R1 mm m0 upper_zero)))))))));
