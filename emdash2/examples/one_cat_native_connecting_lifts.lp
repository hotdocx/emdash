require open emdash.emdash3_2_one_cat_native_cycles_connecting;
require open emdash.emdash3_2_one_cat_native_connecting_upper_lifts;

// Original row/kernel data make θ vanish on every whole map killed by r.
assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T :
  τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C Add t T))
  (Q : τ (@CokernelAdjunctionStructure C Add t T0)) (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (m0 : τ
  (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (lower_zero
  : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T
  R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t
  T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1
  t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (V : τ (Functor B C)) (s : τ
  (@Transf B C V (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)))) (e : τ (@= (@Transf B C V (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0))) (@comp_fapp0 (Functor_cat B C) V
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0))
  (@one_cat_kernel_precomposition_second_transf B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C
  t T R0)) s) (@zero_arrow_family_zero_transf B C t T T0 V (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0))))) ⊢ @one_cat_native_theta_zero_on_r B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 V s e : τ (@= (@Transf B C V (@homology_adjunction_family_func B C Add t
  T T0 P Q (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))) (@comp_fapp0
  (Functor_cat B C) V (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B
  C t T R0)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_covered_homology_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1
  lower_zero E1 E2) s) (@zero_arrow_family_zero_transf B C t T T0 V (@homology_adjunction_family_func B C Add t T
  T0 P Q (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))));
assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T :
  τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C Add t T))
  (Q : τ (@CokernelAdjunctionStructure C Add t T0)) (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (m0 : τ
  (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (lower_zero
  : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T
  R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t
  T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1
  t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (Rm : τ (Functor B
  (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0)) (upper_zero : τ (@= (@Transf
  B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T
  R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1
  m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (Em : τ (@OneCatZeroConeShortExactFamily B C
  Add C1 t T T0 P Q Rm)) ⊢ @one_cat_native_upper_lift_boundary_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1
  lower_zero E0 E1 E2 Rm mm upper_zero Em : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T
  R0 R1 m0))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
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
  (@zero_cone_row_family_outgoing B C t T Rm)));
assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T :
  τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C Add t T))
  (Q : τ (@CokernelAdjunctionStructure C Add t T0)) (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (m0 : τ
  (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (lower_zero
  : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T
  R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t
  T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1
  t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (Rm : τ (Functor B
  (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0)) (upper_zero : τ (@= (@Transf
  B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T
  R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1
  m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (Em : τ (@OneCatZeroConeShortExactFamily B C
  Add C1 t T T0 P Q Rm)) ⊢ @one_cat_native_upper_lift_theta_zero B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2 Rm mm upper_zero Em : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_src) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t
  T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t
  T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t
  T Rm walking_arrow_src) (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C
  t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@one_cat_native_covered_homology_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2)
  (@one_cat_native_upper_lift_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Rm mm upper_zero
  Em)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2))));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (R0 R1 R2 : τ (Functor B
  (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)))) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)) R1 R2)) (lower_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src))
  (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)))) (E0 : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R2)) (Rm : τ (Functor B
  (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)) Rm R0)) (upper_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_src)
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
  A) T0 P Q Rm)) ⊢ @one_cat_native_cycles_connecting_reconstruction B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2 : τ (@= (@Transf B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R0 R1 m0))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R0)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) (@one_cat_native_cycles_connecting_transf B C C1 Prod t A T0 P Q
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R0 R1 m0) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R0))) (@one_cat_native_covered_homology_transf B C (@additive_preadditive
  C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (R0 R1 R2 : τ (Functor B
  (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)))) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)) R1 R2)) (lower_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src))
  (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R0 R1 m0
  walking_arrow_src)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)))) (E0 : τ
  (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R2)) (Rm : τ (Functor B
  (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t
  (@additive_terminal_object C Prod t A)) Rm R0)) (upper_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) Rm walking_arrow_src)
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
  A) T0 P Q Rm)) (other : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R0 R1 m0)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2)))) ⊢ @eq_refl (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R0 R1 m0)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2))) (@one_cat_native_cycles_connecting_transf B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) : τ
  (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R0 R1 m0)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E2))) (@one_cat_native_cycles_connecting_transf B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  other);
