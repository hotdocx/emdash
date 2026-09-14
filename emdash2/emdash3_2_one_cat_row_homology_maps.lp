require open emdash.emdash3_2_one_cat_middle_column_inputs;
require open emdash.emdash3_2_one_cat_homology_family_maps;

// The existing whole row map supplies the incoming column square.
symbol one_cat_row_triple_incoming_diagram_map [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ
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
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
 : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1))
≔ @one_cat_square_family_transf B C C1 (@zero_cone_row_family_source_func B C t T R1)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_source_func B C t T R2)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_source_map B C t T R1 R2
  m1) (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t T R1) (@one_cat_zero_cone_row_family_incoming B C C1 t T R2)
  (@eq_sym _ _ _ (@one_cat_zero_cone_row_incoming_square_path B C C1 t T R1 R2 m1));

// The existing whole row map supplies the outgoing column square.
symbol one_cat_row_triple_outgoing_diagram_map [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ
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
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
 : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1))
≔ @one_cat_square_family_transf B C C1 (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T
  R1 R2 m1 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R1) (@zero_cone_row_family_outgoing B C t T
  R2) (@eq_sym _ _ _ (@one_cat_zero_cone_row_outgoing_square_path B C C1 t T R1 R2 m1));

// Input recovery and original row naturality provide whole incoming compatibility.
symbol one_cat_row_triple_incoming_map_path [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
 : τ (@= (@Transf B C (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_incoming_diagram_map
  B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2) walking_arrow_src) (@zero_arrow_family_incoming_transf
  B C t T (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))) (@comp_fapp0
  (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_arrow_family_incoming_transf B C t T (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) (@one_cat_zero_cone_row_family_incoming B C C1 t T R0)))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_source_func B C t T R1)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@Transf B C
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src))
  (λ v : τ (@Transf B C (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T
  R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  v (@zero_arrow_family_incoming_transf B C t T (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2)))) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t T R1
  R2 m1) (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R1) (@one_cat_square_family_src_path
  B C C1 (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_vertex_func B C t T R2
  walking_arrow_src) (@zero_cone_row_family_source_map B C t T R1 R2 m1) (@zero_cone_row_family_vertex_map B C t T
  R1 R2 m1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R1)
  (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@eq_sym _ _ _
  (@one_cat_zero_cone_row_incoming_square_path B C C1 t T R1 R2 m1)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R1)) (@Transf B C
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src))
  (λ v : τ (@Transf B C (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T
  R1)), (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t T R1) v)) (@zero_arrow_family_incoming_transf B C t T
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2))
  (@zero_cone_row_family_source_map B C t T R0 R1 m0) (@one_cat_kernel_family_input_incoming_path B C C1 t T T0
  (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_row_family_source_map B C t T R0 R1 m0) (@one_cat_zero_cone_left_column_zero_path B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E2))) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@one_cat_zero_cone_row_incoming_square_path B C C1 t T R0 R1 m0)) (@eq_ap (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (@Transf B C (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (λ v : τ (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) v (@one_cat_zero_cone_row_family_incoming B C C1 t T R0))) (@zero_cone_row_family_vertex_map
  B C t T R0 R1 m0 walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) (@eq_sym
  _ _ _ (@one_cat_kernel_family_input_incoming_path B C C1 t T T0 (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) lower_zero))))));

// Input recovery and original row naturality provide whole outgoing compatibility.
symbol one_cat_row_triple_outgoing_map_path [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
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
 : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) (@sym_transf_tapp0_transf B
  WalkingArrow_cat C (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_outgoing_diagram_map B C Add
  C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2) walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)))
  (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt) (@zero_arrow_family_incoming_transf B C t T (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
  (@zero_cone_row_family_outgoing B C t T R0)))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt)) (λ v : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) v
  (@zero_arrow_family_incoming_transf B C t T (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)))) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_right_column_outgoing_func B C t T
  R1 R2 m1) (@one_cat_row_triple_outgoing_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) walking_arrow_src) (@zero_cone_row_family_outgoing B C t T R1) (@one_cat_square_family_src_path B C C1
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) (@zero_cone_row_family_vertex_map B C t T R1 R2
  m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R1) (@zero_cone_row_family_outgoing B C t T R2) (@eq_sym _ _ _
  (@one_cat_zero_cone_row_outgoing_square_path B C C1 t T R1 R2 m1)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (λ v : τ (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R1) v))
  (@zero_arrow_family_incoming_transf B C t T (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B
  C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
  (@one_cat_kernel_family_input_incoming_path B C C1 t T T0 (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src) lower_zero)) (@eq_trans _ _ _ _ (@eq_sym _
  _ _ (@one_cat_zero_cone_row_outgoing_square_path B C C1 t T R0 R1 m0)) (@eq_ap (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt)) (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (λ v : τ (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) v (@zero_cone_row_family_outgoing B C t T R0)))
  (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_tgt) (@zero_arrow_family_incoming_transf B C t
  T (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  T R1 R2 m1) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@eq_sym
  _ _ _ (@one_cat_kernel_family_input_incoming_path B C C1 t T T0 (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_row_family_vertex_map B
  C t T R0 R1 m0 walking_arrow_tgt) (@one_cat_zero_cone_right_column_zero_path B C Add C1 t T T0 P Q R0 R1 R2 m0
  m1 lower_zero E0)))))));

// Original K/Q actions induce the whole homology map of the incoming row maps.
symbol one_cat_row_triple_incoming_homology_map [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ
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
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
 : τ (@Transf B C (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T
  R0) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T
  T0 P Q R0 R1 R2 m0 m1 lower_zero E2)) (@homology_adjunction_family_func B C Add t T T0 P Q
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)))
≔ @one_cat_homology_family_map_transf B C Add C1 t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input
  B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2) (@one_cat_zero_cone_middle_column_input B C C1 t T T0
  R0 R1 R2 m0 m1 lower_zero) (@one_cat_zero_cone_row_family_incoming B C C1 t T R0)
  (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_row_triple_incoming_map_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2);

// Original K/Q actions induce the whole homology map of the outgoing row maps.
symbol one_cat_row_triple_outgoing_homology_map [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ
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
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
 : τ (@Transf B C (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0)))
≔ @one_cat_homology_family_map_transf B C Add C1 t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_right_column_outgoing_func B C t T
  R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0)
  (@zero_cone_row_family_outgoing B C t T R0) (@one_cat_row_triple_outgoing_diagram_map B C Add C1 t T T0 P
  Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_row_triple_outgoing_map_path B C Add C1 t T T0 P Q R0 R1
  R2 m0 m1 lower_zero E0 E1 E2);

// The original cycle-map inclusion is the original whole row map after its kernel inclusion.
symbol one_cat_row_triple_incoming_cycle_projection_path [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1
  : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1
  : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (lower_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
  m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ (@OneCatZeroConeShortExactFamily B C
  Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C
  Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C Add C1 t T T0 P Q (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_source_func B C t T R1)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1
  t T R1) (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1))))
≔ (@eq_trans _ _ _ _ (@one_cat_kernel_family_map_inclusion_path B C Add C1 t T T0 P Q
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t T R1
  R2 m1) (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1
  E2)) (@eq_ap (@Transf B C (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C
  t T R1 walking_arrow_src)) (@Transf B C (@kernel_adjunction_family_func B C Add t T P
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src)) (λ v : τ (@Transf B C (@zero_cone_row_family_source_func B C t T R1)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
  (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  v (@kernel_adjunction_family_inclusion_transf B C Add t T P (@zero_cone_left_column_outgoing_func B C t T R1 R2
  m1)))) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_incoming_diagram_map
  B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2) walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t T R1) (@one_cat_square_family_src_path B C C1
  (@zero_cone_row_family_source_func B C t T R1) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
  (@zero_cone_row_family_source_map B C t T R1 R2 m1) (@zero_cone_row_family_vertex_map B C t T R1 R2 m1
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T R1)
  (@one_cat_zero_cone_row_family_incoming B C C1 t T R2) (@eq_sym _ _ _
  (@one_cat_zero_cone_row_incoming_square_path B C C1 t T R1 R2 m1)))));

// The original cycle-map inclusion is the original whole row map after its kernel inclusion.
symbol one_cat_row_triple_outgoing_cycle_projection_path [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1
  : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1
  : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (lower_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
  m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ (@OneCatZeroConeShortExactFamily B C
  Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func
  B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B
  C) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2
  m1)) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf B C
  Add t T P (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)) (@kernel_adjunction_family_map_transf
  B C Add C1 t T T0 P Q (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1) (@one_cat_row_triple_outgoing_diagram_map B C Add
  C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T R1) (@kernel_adjunction_family_inclusion_transf B C
  Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1))))
≔ (@eq_trans _ _ _ _ (@one_cat_kernel_family_map_inclusion_path B C Add C1 t T T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_right_column_outgoing_func B C t T
  R1 R2 m1) (@one_cat_row_triple_outgoing_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1
  E2)) (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (@Transf B C (@kernel_adjunction_family_func B
  C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)) (@zero_cone_row_family_vertex_func
  B C t T R1 walking_arrow_tgt)) (λ v : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)), (@comp_fapp0 (Functor_cat
  B C) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B C t T R1 R2
  m1)) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T
  R1 walking_arrow_tgt) v (@kernel_adjunction_family_inclusion_transf B C Add t T P
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)))) (@sym_transf_tapp0_transf B WalkingArrow_cat
  C (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_right_column_outgoing_func B C t T
  R1 R2 m1) (@one_cat_row_triple_outgoing_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) walking_arrow_src) (@zero_cone_row_family_outgoing B C t T R1) (@one_cat_square_family_src_path B C C1
  (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
  walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) (@zero_cone_row_family_vertex_map B C t T R1 R2
  m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t T R1) (@zero_cone_row_family_outgoing B C t T R2) (@eq_sym _ _ _
  (@one_cat_zero_cone_row_outgoing_square_path B C C1 t T R1 R2 m1)))));

// The original incoming homology map reconstructs the induced cycle map after q_A.
symbol one_cat_row_triple_incoming_homology_projection_path [B C : Cat] [Add : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1
  : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (lower_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
  m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ (@OneCatZeroConeShortExactFamily B C
  Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_left_column_outgoing_func B C t T
  R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))) (@comp_fapp0
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
  (@one_cat_row_triple_incoming_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))))
≔ @one_cat_homology_family_map_projection_path B C Add C1 t T T0 P Q (@zero_cone_row_family_source_func B C
  t T R0) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_left_column_outgoing_func B
  C t T R1 R2 m1) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)
  (@one_cat_zero_cone_row_family_incoming B C C1 t T R0) (@one_cat_row_triple_incoming_diagram_map B C Add
  C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_row_triple_incoming_map_path B C Add C1 t T T0
  P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2);

// The original outgoing homology map reconstructs the induced cycle map after q_M.
symbol one_cat_row_triple_outgoing_homology_projection_path [B C : Cat] [Add : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1
  : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (lower_zero : τ (@= (@Transf B C
  (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R1 R2
  m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ (@OneCatZeroConeShortExactFamily B C
  Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R1)) (E2 : τ
  (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func
  B C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t
  T R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))) (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C Add t T P (@zero_cone_middle_column_outgoing_func B
  C t T R1 R2 m1)) (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T
  R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero))
  (@homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0))
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
  (@one_cat_row_triple_outgoing_diagram_map B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))))
≔ @one_cat_homology_family_map_projection_path B C Add C1 t T T0 P Q (@zero_cone_row_family_vertex_func B C
  t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
  (@zero_cone_middle_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_right_column_outgoing_func B C t T
  R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t T T0 R0 R1 R2 m0 m1 lower_zero)
  (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E0)
  (@zero_cone_row_family_outgoing B C t T R0) (@one_cat_row_triple_outgoing_diagram_map B C Add C1 t T T0 P
  Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_row_triple_outgoing_map_path B C Add C1 t T T0 P Q R0 R1
  R2 m0 m1 lower_zero E0 E1 E2);
