/* Covered left-homology map from the original native row window.
   No splitting, cover epicity or final δ is supplied by these constructions. */
require open emdash.emdash3_2_one_cat_zero_cone_column_inputs;
require open emdash.emdash3_2_one_cat_short_exact_family_lifts;
require open emdash.emdash3_2_one_cat_homology_cover_maps;

// The native row square and original kernel law give the next-row annihilation.
symbol one_cat_native_cover_row_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (R0 R1 : τ (Functor B (@ZeroArrowCone_cat C t T)))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1))
  : τ (@= (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C
    t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1
    walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R1 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R1) (@comp_fapp0 (Functor_cat B C)
    (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@kernel_precomposition_first_transf B
    C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
    R0)))) (@zero_arrow_family_zero_transf B C t T T0 (@kernel_precomposition_family_func B C Add t T P
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)))
≔ (@eq_trans (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B
  C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func
  B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t
  T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R1) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func
  B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C
  t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
  (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) (@comp_fapp0 (Functor_cat
  B C) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
  B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_tgt) (@zero_cone_row_family_outgoing B
  C t T R0)) (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0))) (@zero_arrow_family_zero_transf B C t T T0
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt)) (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (@Transf B C
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt)) (λ s : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) s
  (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)))) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C
  t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R1) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) (@zero_cone_row_family_vertex_map B C t
  T R0 R1 m0 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R0)) (@eq_sym (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C
  t T R1 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) (@zero_cone_row_family_vertex_map B C t
  T R0 R1 m0 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R0)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C
  t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R1) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0
  walking_arrow_src)) (@one_cat_zero_cone_row_outgoing_square_path B C C1 t T R0 R1 m0)))
  (@one_cat_kernel_precomposition_projection_zero_path B C Add C1 t T T0 P (@zero_cone_row_family_vertex_func B
  C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)));

// Lift the covered middle differential through the actual next-row β inverse.
symbol one_cat_native_cover_left_lift [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 : τ (Functor B (@ZeroArrowCone_cat C t T))) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (E1 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) : τ (@Transf B C
    (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1))
≔ @one_cat_short_exact_family_lift B C Add C1 t T T0 P Q (@zero_cone_row_family_source_func B C t T R1)
  (@zero_cone_row_family_diagram_func B C t T R1) (@one_cat_zero_cone_row_family_transf B C C1 t T R1) E1
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@kernel_precomposition_first_transf B C
  Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)))
  (@one_cat_native_cover_row_zero B C Add C1 t T T0 P R0 R1 m0);

// The original row inclusion recovers the original covered middle differential.
symbol one_cat_native_cover_left_reconstruction [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 : τ (Functor B (@ZeroArrowCone_cat C t T))) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (E1 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1))
  : τ (@= (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C
    t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1
    walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
    (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1
    walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R1)
    (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1)) (@comp_fapp0 (Functor_cat B C)
    (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@kernel_precomposition_first_transf B
    C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
    R0))))
≔ @one_cat_short_exact_family_lift_reconstruction B C Add C1 t T T0 P Q (@zero_cone_row_family_source_func
  B C t T R1) (@zero_cone_row_family_diagram_func B C t T R1) (@one_cat_zero_cone_row_family_transf B C C1
  t T R1) E1 (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@kernel_precomposition_first_transf B C
  Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)))
  (@one_cat_native_cover_row_zero B C Add C1 t T T0 P R0 R1 m0);

// Row2 cancellation and the whole middle chain law make the lift a left cycle.
symbol one_cat_native_cover_left_zero [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T)))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (z : τ
    (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
    T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E1 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B
    C Add C1 t T T0 P Q R2))
  : τ (@= (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C
    t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R2))
    (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
    (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_source_func B C t T R2)
    (@zero_cone_row_family_source_map B C t T R1 R2 m1) (@one_cat_native_cover_left_lift B C Add C1 t T T0
    P Q R0 R1 m0 E1)) (@zero_arrow_family_zero_transf B C t T T0 (@kernel_precomposition_family_func B C Add t T P
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
    (@zero_cone_row_family_source_func B C t T R2)))
≔ @one_cat_short_exact_family_incoming_reflect_path B C Add C1 t T T0 P Q (@zero_cone_row_family_source_func B C
  t T R2) (@zero_cone_row_family_diagram_func B C t T R2) (@one_cat_zero_cone_row_family_transf B C C1 t T
  R2) E2
    (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@comp_fapp0 (Functor_cat B C)
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_source_map B C t T R1 R2 m1)
      (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1)) (@zero_arrow_family_zero_transf B C t
      T T0 (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R2))
      (@eq_trans (@Transf B C (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R2)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@comp_fapp0 (Functor_cat B C)
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_source_map B C t T R1 R2 m1)
      (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1))) (@comp_fapp0 (Functor_cat B C)
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@comp_fapp0 (Functor_cat B C)
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R1) (@one_cat_native_cover_left_lift B C Add C1 t
      T T0 P Q R0 R1 m0 E1))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@zero_arrow_family_zero_transf
      B C t T T0 (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R2)))
      (@eq_ap (@Transf B C (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@Transf B C
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src)) (λ s : τ (@Transf B C (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) s (@one_cat_native_cover_left_lift
      B C Add C1 t T T0 P Q R0 R1 m0 E1))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C
      t T R1) (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R2)
      (@zero_cone_row_family_source_map B C t T R1 R2 m1)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R1)) (@eq_sym (@Transf B C
      (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R1)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_source_func B C t T R2)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@zero_cone_row_family_source_map B C t T R1
      R2 m1)) (@one_cat_zero_cone_row_incoming_square_path B C C1 t T R1 R2 m1))) (@eq_trans (@Transf B C
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B
      C t T R1 R2 m1 walking_arrow_src) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T
      P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1
      walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R1)
      (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1))) (@comp_fapp0 (Functor_cat B C)
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@comp_fapp0 (Functor_cat B C)
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@kernel_precomposition_first_transf
      B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@zero_arrow_family_zero_transf
      B C t T T0 (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R2)))
      (@eq_ap (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func
      B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1
      walking_arrow_src)) (@Transf B C (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (λ s : τ (@Transf B C
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R1
      walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B
      C t T R1 R2 m1 walking_arrow_src) s)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add
      t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1
      walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R1)
      (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1)) (@comp_fapp0 (Functor_cat B C)
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) (@kernel_precomposition_first_transf
      B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0))) (@one_cat_native_cover_left_reconstruction B C Add C1 t T T0 P Q R0 R1 m0 E1)) (@eq_trans (@Transf B
      C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B
      C t T R1 R2 m1 walking_arrow_src) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T
      P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B
      C t T R0 R1 m0 walking_arrow_src) (@kernel_precomposition_first_transf B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_arrow_family_zero_transf B C t T
      T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@kernel_precomposition_first_transf B C
      Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@zero_arrow_family_zero_transf
      B C t T T0 (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R2)))
      (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@Transf B C
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src)) (λ s : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) s
      (@kernel_precomposition_first_transf B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)))) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C
      t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) z) (@eq_trans (@Transf B C
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_arrow_family_zero_transf B C t T
      T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@kernel_precomposition_first_transf B C
      Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0))) (@zero_arrow_family_zero_transf B C t T T0 (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R2)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@zero_arrow_family_zero_transf B C t T T0
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R2)))
      (@one_cat_zero_family_precompose_path B C C1 t T T0 (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@kernel_precomposition_first_transf B C
      Add t T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0))) (@eq_sym (@Transf B C (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R2)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@zero_arrow_family_zero_transf B C t T T0
      (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R2)))
      (@zero_arrow_family_zero_transf B C t T T0 (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))
      (@one_cat_zero_family_postcompose_path B C C1 t T T0 (@kernel_precomposition_family_func B C Add t T P
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T
      R0)) (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R2)))))));

// The original left outgoing K receives that cycle by the existing native mate.
symbol one_cat_native_cover_left_cycles [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T)))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (z : τ
    (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
    T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E1 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B
    C Add C1 t T T0 P Q R2)) : τ (@Transf B C (@kernel_precomposition_family_func B C Add t T P
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
    (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)))
≔ @one_cat_kernel_family_lift B C Add C1 t T T0 P (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func
  B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_left_column_outgoing_func B C
  t T R1 R2 m1) (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1)
  (@one_cat_native_cover_left_zero B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E1 E2);

// Its original inclusion reconstructs the entire left lift.
symbol one_cat_native_cover_cycles_reconstruction [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T)))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (z : τ
    (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
    T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E1 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B
    C Add C1 t T T0 P Q R2))
  : τ (@= (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C
    t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@zero_cone_row_family_outgoing B C t T R0)) (@zero_cone_row_family_source_func B C t T R1))
    (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
    (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
    (@zero_cone_row_family_source_func B C t T R1) (@kernel_adjunction_family_inclusion_transf B C Add t T P
    (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@one_cat_native_cover_left_cycles B C Add C1
    t T T0 P Q R0 R1 R2 m0 m1 z E1 E2)) (@one_cat_native_cover_left_lift B C Add C1 t T T0 P Q R0 R1 m0 E1))
≔ @one_cat_kernel_family_lift_ambient_reconstruction B C Add C1 t T T0 P (@kernel_precomposition_family_func B C Add t
  T P (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0))
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_native_cover_left_lift B C Add C1 t T
  T0 P Q R0 R1 m0 E1) (@one_cat_native_cover_left_zero B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E1 E2);

// θ is the original left H quotient after that same cycle lift.
symbol one_cat_native_covered_homology_transf [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T)))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (z : τ
    (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
    T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E1 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B
    C Add C1 t T T0 P Q R2))
  : τ (@Transf B C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T
    R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@zero_cone_row_family_outgoing B C t T R0)) (@homology_adjunction_family_func B C Add t T T0 P Q
    (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
    (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E2)))
≔ (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C Add t T P
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func
  B C t T R0 R1 m0) (@zero_cone_row_family_outgoing B C t T R0)) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E2))
  (@homology_adjunction_family_projection_transf B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T
  R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C
  Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E2)) (@one_cat_native_cover_left_cycles B C Add C1 t T T0 P Q R0 R1 R2 m0
  m1 z E1 E2));
