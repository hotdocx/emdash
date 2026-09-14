/* Four-row native assembly: same pullback source, original H endpoints, whole action. */
require open emdash.emdash3_2_one_cat_native_homology_window_maps;

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm
    R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@=
    (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
    m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C Add
    C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
  ⊢ (@one_cat_native_window_source_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
    E0 E1 E2) ≡ (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T Rm
    walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@one_cat_native_window_right_column_input B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
    E1 E2));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm
    R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@=
    (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
    m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C Add
    C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
  ⊢ (@one_cat_native_window_target_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
    E0 E1 E2) ≡ (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
    (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_native_window_left_column_input B C Add C1 t T
    T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm
    R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@=
    (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
    m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C Add
    C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
  ⊢ (@one_cat_native_window_cover_transf B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
    : τ (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t
    T R0)) (@one_cat_native_window_source_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
    lower_zero Em E0 E1 E2));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm
    R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@=
    (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
    m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C Add
    C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
  ⊢ (@one_cat_native_window_covered_transf B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
    E2) : τ (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
    R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
    t T R0)) (@one_cat_native_window_target_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
    lower_zero Em E0 E1 E2));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm
    R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@=
    (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
    m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C Add
    C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (x : τ (Obj B))
  ⊢ (@tapp0_fapp0 B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t
    T R0)) (@one_cat_native_window_source_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
    lower_zero Em E0 E1 E2) x (@one_cat_native_window_cover_transf B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1
    upper_zero lower_zero Em E0 E1 E2)) ≡ (@comp_fapp0 C (@fapp0 B C (@kernel_precomposition_family_func B C Add t T P
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0
    R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) x) (@fapp0 B C (@kernel_adjunction_family_func B C Add t T P
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) x) (@fapp0 B C
    (@one_cat_native_window_source_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
    E0 E1 E2) x) (@tapp0_fapp0 B C (@kernel_adjunction_family_func B C Add t T P
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) (@one_cat_native_window_source_homology_func B C Add C1
    t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2) x
    (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T Rm
    walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@one_cat_native_window_right_column_input B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
    E1 E2))) (@tapp0_fapp0 B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B
    C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)) x (@one_cat_kernel_precomposition_second_transf B C Add
    C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm
    R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@=
    (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
    m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C Add
    C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (x y : τ (Obj B))
  ⊢ (@tapp1_func B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t
    T R0)) (@one_cat_native_window_source_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
    lower_zero Em E0 E1 E2) x y (@one_cat_native_window_cover_transf B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1
    upper_zero lower_zero Em E0 E1 E2)) : τ (Functor (Hom_cat B x y) (Hom_cat C (@fapp0 B C
    (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) x) (@fapp0 B
    C (@one_cat_native_window_source_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
    E0 E1 E2) y)));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm
    R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@=
    (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
    m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C Add
    C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (x : τ (Obj B))
  ⊢ (@tapp0_fapp0 B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t
    T R0)) (@one_cat_native_window_target_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
    lower_zero Em E0 E1 E2) x (@one_cat_native_window_covered_transf B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1
    upper_zero lower_zero Em E0 E1 E2)) ≡ (@comp_fapp0 C (@fapp0 B C (@kernel_precomposition_family_func B C Add t T P
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0
    R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) x) (@fapp0 B C (@kernel_adjunction_family_func B C Add t T P
    (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) x) (@fapp0 B C
    (@one_cat_native_window_target_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
    E0 E1 E2) x) (@tapp0_fapp0 B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func
    B C t T R1 R2 m1)) (@one_cat_native_window_target_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1
    upper_zero lower_zero Em E0 E1 E2) x (@homology_adjunction_family_projection_transf B C Add t T T0 P Q
    (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
    (@one_cat_native_window_left_column_input B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0
    E1 E2))) (@tapp0_fapp0 B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B
    C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
    (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) x (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P
    Q R0 R1 R2 m0 m1 lower_zero E1 E2)));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm
    R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@=
    (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
    m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C Add
    C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (x y : τ (Obj B))
  ⊢ (@tapp1_func B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t
    T R0)) (@one_cat_native_window_target_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero
    lower_zero Em E0 E1 E2) x y (@one_cat_native_window_covered_transf B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1
    upper_zero lower_zero Em E0 E1 E2)) : τ (Functor (Hom_cat B x y) (Hom_cat C (@fapp0 B C
    (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) x) (@fapp0 B
    C (@one_cat_native_window_target_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
    E0 E1 E2) y)));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm
    R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@=
    (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
    m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C Add
    C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
  ⊢ (@one_cat_native_cover_cycles_reconstruction B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2) : τ (@=
    (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t
    T R0)) (@zero_cone_row_family_source_func B C t T R1)) (@comp_fapp0 (Functor_cat B C)
    (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
    (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
    (@zero_cone_row_family_source_func B C t T R1) (@kernel_adjunction_family_inclusion_transf B C Add t T P
    (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q
    R0 R1 R2 m0 m1 lower_zero E1 E2)) (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1));

assertnot [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm
    R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@=
    (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
    m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C Add
    C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (Q2 : τ (@CokernelAdjunctionStructure C Add t T0))
  ⊢ (@one_cat_native_window_covered_transf B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
    E2) : τ (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
    R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
    t T R0)) (@homology_adjunction_family_func B C Add t T T0 P Q2 (@zero_cone_row_family_source_func B C t T R0)
    (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_native_window_left_column_input B C Add C1 t T
    T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)));

assertnot [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm
    R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@=
    (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
    m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ (@OneCatZeroConeShortExactFamily B C Add
    C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (p2 : τ (@Transf B C
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_tgt)))
  ⊢ (@one_cat_native_window_cover_transf B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
    : τ (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) p2)
    (@one_cat_native_window_source_homology_func B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
    E0 E1 E2));
