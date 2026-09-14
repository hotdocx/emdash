/* Whole column-zero derivation from native row action and row cancellation. */
require open emdash.emdash3_2_one_cat_zero_cone_row_families;
require open emdash.emdash3_2_one_cat_zero_family_postcomposition_paths;
require open emdash.emdash3_2_one_cat_kernel_input_observation_paths;

// The left column is a chain by the original incoming map at row2.
symbol one_cat_zero_cone_left_column_zero_path [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
  : τ (@= (@Transf B C (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B
    C t T R2)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0)
    (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_source_func B C t T R2)
    (@zero_cone_row_family_source_map B C t T R1 R2 m1) (@zero_cone_row_family_source_map B C t T R0 R1
    m0)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_source_func B C t T R0)
    (@zero_cone_row_family_source_func B C t T R2)))
≔ @one_cat_short_exact_family_incoming_reflect_path B C Add C1 t T T0 P Q (@zero_cone_row_family_source_func B C
  t T R2) (@zero_cone_row_family_diagram_func B C t T R2) (@one_cat_zero_cone_row_family_transf B C C1 t T
  R2) E2
    (@zero_cone_row_family_source_func B C t T R0) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_source_map B C t T R1 R2 m1)
      (@zero_cone_row_family_source_map B C t T R0 R1 m0)) (@zero_arrow_family_zero_transf B C t T T0
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R2))
      (@eq_trans (@Transf B C (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R2)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_source_map B C t T R1 R2 m1)
      (@zero_cone_row_family_source_map B C t T R0 R1 m0))) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R1
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R1) (@zero_cone_row_family_source_map B C t T R0
      R1 m0))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@zero_arrow_family_zero_transf
      B C t T T0 (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T
      R2))) (@eq_ap (@Transf B C (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@Transf B C
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src)) (λ u : τ (@Transf B C (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) u (@zero_cone_row_family_source_map
      B C t T R0 R1 m0))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_vertex_func B C t T R2
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
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
      (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1
      walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R1)
      (@zero_cone_row_family_source_map B C t T R0 R1 m0))) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@comp_fapp0
      (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R0)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R2)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@zero_arrow_family_zero_transf B C t T T0
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R2)))
      (@eq_ap (@Transf B C (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@Transf B C
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src)) (λ u : τ (@Transf B C (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R1
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) u)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R1) (@zero_cone_row_family_source_map B C t T R0
      R1 m0)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R0)) (@eq_sym (@Transf B C
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R1
      walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R0)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R1)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R1) (@zero_cone_row_family_source_map B C t T R0
      R1 m0)) (@one_cat_zero_cone_row_incoming_square_path B C C1 t T R0 R1 m0))) (@eq_trans (@Transf B C
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_src) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B
      C t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R0)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R0)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R2)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@zero_arrow_family_zero_transf B C t T T0
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R2)))
      (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@Transf B C
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src)) (λ u : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) u
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R0))) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C
      t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) z) (@eq_trans (@Transf B C
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_src) (@zero_arrow_family_zero_transf B C t T T0
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_src)) (@one_cat_zero_cone_row_family_incoming B C C1 t T R0))
      (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R2)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@zero_arrow_family_zero_transf B C t T T0
      (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R2)))
      (@one_cat_zero_family_precompose_path B C C1 t T T0 (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R0)) (@eq_sym (@Transf B
      C (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@zero_arrow_family_zero_transf
      B C t T T0 (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T
      R2))) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))
      (@one_cat_zero_family_postcompose_path B C C1 t T T0 (@zero_cone_row_family_source_func B C t T R0)
      (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_vertex_func B C t T R2
      walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R2)))))));

// The right column is a chain by the original outgoing map at row0.
symbol one_cat_zero_cone_right_column_zero_path [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0))
  : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B
    C t T R1 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)
    (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_tgt)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_tgt)) (@zero_arrow_family_zero_transf B C t
    T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)))
≔ @one_cat_short_exact_family_outgoing_reflect_path B C Add C1 t T T0 P Q (@zero_cone_row_family_source_func B C
  t T R0) (@zero_cone_row_family_diagram_func B C t T R0) (@one_cat_zero_cone_row_family_transf B C C1 t T
  R0) E0
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func
      B C t T R1 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)
      (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_tgt)
      (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_tgt)) (@zero_arrow_family_zero_transf B C
      t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)) (@eq_trans (@Transf B C
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T
      R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func
      B C t T R1 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)
      (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_tgt)
      (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_tgt))
      (@zero_cone_row_family_outgoing B C t T R0)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R1 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)
      (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
      (@zero_cone_row_family_outgoing B C t T R1) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0
      walking_arrow_src))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) (@zero_arrow_family_zero_transf B C t T
      T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)) (@zero_cone_row_family_outgoing B
      C t T R0)) (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (@Transf B C
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_tgt)) (λ u : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)), (@comp_fapp0
      (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_tgt) (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_tgt) u))
      (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func
      B C t T R1 walking_arrow_tgt) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_tgt)
      (@zero_cone_row_family_outgoing B C t T R0)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
      (@zero_cone_row_family_outgoing B C t T R1) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0
      walking_arrow_src)) (@one_cat_zero_cone_row_outgoing_square_path B C C1 t T R0 R1 m0)) (@eq_trans (@Transf
      B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R1 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)
      (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
      (@zero_cone_row_family_outgoing B C t T R1) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0
      walking_arrow_src))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C
      t T R2) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)
      (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt))
      (@zero_cone_row_family_outgoing B C t T R0)) (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func
      B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)) (@Transf B
      C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)) (λ u : τ (@Transf B C
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T
      R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) u (@zero_cone_row_family_vertex_map
      B C t T R0 R1 m0 walking_arrow_src))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B
      C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) (@zero_cone_row_family_vertex_map B
      C t T R1 R2 m1 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R1)) (@comp_fapp0 (Functor_cat B
      C) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R2)
      (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src))
      (@one_cat_zero_cone_row_outgoing_square_path B C C1 t T R1 R2 m1)) (@eq_trans (@Transf B C
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T
      R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C
      t T R2) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)
      (@zero_cone_row_family_outgoing B C t T R2) (@zero_arrow_family_zero_transf B C t T T0
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_src))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T
      R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) (@zero_arrow_family_zero_transf B C t T
      T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)) (@zero_cone_row_family_outgoing B
      C t T R0)) (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@Transf B C
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_tgt)) (λ u : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)), (@comp_fapp0
      (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R2) u)) (@comp_fapp0 (Functor_cat B
      C) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C
      t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) z) (@eq_trans (@Transf B C
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T
      R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C
      t T R2) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))
      (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)) (@comp_fapp0
      (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_tgt) (@zero_arrow_family_zero_transf B C t T T0
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_tgt)) (@zero_cone_row_family_outgoing B C t T R0))
      (@one_cat_zero_family_postcompose_path B C C1 t T T0 (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C
      t T R2)) (@eq_sym (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)
      (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0
      walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt))
      (@zero_cone_row_family_outgoing B C t T R0)) (@zero_arrow_family_zero_transf B C t T T0
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R2 walking_arrow_tgt)) (@one_cat_zero_family_precompose_path B C C1 t T T0
      (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func
      B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)
      (@zero_cone_row_family_outgoing B C t T R0)))))));

// The left outgoing diagram precedes all K/Q and short-exact choices.
symbol zero_cone_left_column_outgoing_func [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) : τ
    (Functor B (Functor_cat WalkingArrow_cat C))
≔ @transf_arrow_diagram_func B C (@zero_cone_row_family_source_func B C t T R1)
  (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_source_map B C t T R1 R2 m1);

// The derived whole zero feeds the existing native input constructor.
symbol one_cat_zero_cone_left_column_input [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
  : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) (@zero_cone_row_family_source_func B C t T R0))
    (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
≔ @one_cat_kernel_family_input B C C1 t T T0 (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_row_family_source_map B C t T R0 R1
  m0)
    (@one_cat_zero_cone_left_column_zero_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E2);

// The right outgoing diagram precedes all K/Q and short-exact choices.
symbol zero_cone_right_column_outgoing_func [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) : τ
    (Functor B (Functor_cat WalkingArrow_cat C))
≔ @transf_arrow_diagram_func B C (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) (@zero_cone_row_family_vertex_map B C t
  T R1 R2 m1 walking_arrow_tgt);

// The derived whole zero feeds the existing native input constructor.
symbol one_cat_zero_cone_right_column_input [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0))
  : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt))
    (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1))
≔ @one_cat_kernel_family_input B C C1 t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_row_family_vertex_map B C t T R0 R1
  m0 walking_arrow_tgt)
    (@one_cat_zero_cone_right_column_zero_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E0);
