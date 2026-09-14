/* The corrected middle cycle lifts into the original left cycle object. */
require open emdash.emdash3_2_one_cat_middle_homology_representatives;
require open emdash.emdash3_2_one_cat_short_exact_family_lifts;

// The corrected cycle is annihilated by the original middle row projection.
symbol one_cat_middle_corrected_row_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  A) T0 P Q R2))
 : τ (@= (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R1) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_corrected_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N
  R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t
  (@additive_terminal_object C Prod t A) R1) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_corrected_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@eq_trans
  _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)) (@Transf B C (@one_cat_middle_row_cover_func
  B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)) (λ v : τ (@Transf B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)),
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt) v (@one_cat_middle_corrected_cycles B C C1
  Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)))
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@eq_sym _ _ _
  (@one_cat_row_triple_outgoing_cycle_projection_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_sym
  _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0
  m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_corrected_cycles B C C1 Prod t A
  T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))) (@Transf B C
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)) (λ v : τ
  (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))), (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)) v))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_corrected_cycles B C C1 Prod t A
  T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)))
  (@one_cat_middle_corrected_right_cycles_zero B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_zero_family_postcompose_path B C C1 t (@additive_terminal_object C Prod t A) T0
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_tgt)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2
  m1)))))));

// The original short-exact row lifts the corrected cycle into its original left object.
symbol one_cat_middle_corrected_left_lift [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  A) T0 P Q R2))
 : τ (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1))
≔ @one_cat_short_exact_family_lift B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_diagram_func B C t (@additive_terminal_object C Prod t A) R1)
  (@one_cat_zero_cone_row_family_transf B C C1 t (@additive_terminal_object C Prod t A) R1) E1
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_corrected_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_middle_corrected_row_zero B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2);

// The original incoming row map reconstructs the covered corrected cycle.
symbol one_cat_middle_corrected_left_reconstruction [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  A) T0 P Q R2))
 : τ (@= (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1)
  (@one_cat_middle_corrected_left_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_corrected_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
≔ @one_cat_short_exact_family_lift_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R1) (@zero_cone_row_family_diagram_func B C t (@additive_terminal_object
  C Prod t A) R1) (@one_cat_zero_cone_row_family_transf B C C1 t (@additive_terminal_object C Prod t A) R1) E1
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_corrected_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_middle_corrected_row_zero B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2);

// Original lower-row cancellation proves that the lifted left element is a whole cycle.
symbol one_cat_middle_corrected_left_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  A) T0 P Q R2))
 : τ (@= (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R2)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R2)
  (@zero_cone_row_family_source_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_middle_corrected_left_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R2)))
≔ @one_cat_short_exact_family_incoming_reflect_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R2) (@zero_cone_row_family_diagram_func B C t (@additive_terminal_object
  C Prod t A) R2) (@one_cat_zero_cone_row_family_transf B C C1 t (@additive_terminal_object C Prod t A) R2) E2
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R2)
  (@zero_cone_row_family_source_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_middle_corrected_left_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R2)) (@eq_trans _ _ _ _
  (@comp_assoc (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R2)
  (@zero_cone_row_family_source_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_middle_corrected_left_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_source_func B C t (@additive_terminal_object C
  Prod t A) R1) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2
  walking_arrow_src)) (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2
  walking_arrow_src)) (λ v : τ (@Transf B C (@zero_cone_row_family_source_func B C t (@additive_terminal_object C
  Prod t A) R1) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2
  walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod
  t A) R1) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src) v
  (@one_cat_middle_corrected_left_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A)
  R1) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R2)
  (@zero_cone_row_family_source_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1)) (@comp_fapp0
  (Functor_cat B C) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1)) (@eq_sym _ _ _
  (@one_cat_zero_cone_row_incoming_square_path B C C1 t (@additive_terminal_object C Prod t A) R1 R2 m1)))
  (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1
  Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R1) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1)
  (@one_cat_middle_corrected_left_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2
  m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)) (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2
  walking_arrow_src)) (λ v : τ (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1
  R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod
  t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2
  walking_arrow_src) (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1
  walking_arrow_src) v)) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P
  Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C
  Prod t A) R1) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1)
  (@one_cat_middle_corrected_left_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_corrected_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_middle_corrected_left_reconstruction B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0
  P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1 walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_corrected_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@eq_trans
  _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R2 walking_arrow_src)) (@Transf B C (@one_cat_middle_row_cover_func
  B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R2 walking_arrow_src)) (λ v : τ (@Transf B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)),
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R2 walking_arrow_src) v (@one_cat_middle_corrected_cycles B C C1
  Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t (@additive_terminal_object C Prod t A) R1 R2 m1 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@kernel_adjunction_family_func
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src))
  (@one_cat_kernel_family_annihilation_path B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2
  m1))) (@eq_trans _ _ _ _ (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A)
  T0 (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)
  (@one_cat_middle_corrected_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@eq_sym _
  _ _ (@one_cat_zero_family_postcompose_path B C C1 t (@additive_terminal_object C Prod t A) T0
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R2 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R2))))))))));

// The native K mate retains the original left cycle object.
symbol one_cat_middle_left_cycle_lift [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ
  (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0
  P Q)) (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)))) (m0 : τ
  (@Transf B (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R0 R1)) (m1 : τ (@Transf B
  (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t A)) R1 R2)) (lower_zero : τ (@= (@Transf B C
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
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R2))
 : τ (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)))
≔ @one_cat_kernel_family_lift B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A)
  T0 P (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_middle_corrected_left_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_corrected_left_zero B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2);

// The original left kernel inclusion recovers the same row lift.
symbol one_cat_middle_left_cycle_reconstruction [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
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
  A) T0 P Q R2))
 : τ (@= (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_left_cycle_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_middle_corrected_left_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
≔ @one_cat_kernel_family_lift_ambient_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1
  R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A)
  R1 R2 m1) (@one_cat_middle_corrected_left_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@one_cat_middle_corrected_left_zero B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2);

// Original K cancellation identifies the induced left cycle with the corrected middle cycle.
symbol one_cat_middle_left_cycle_map_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  A) T0 P Q R2))
 : τ (@= (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_left_cycle_lift B C C1 Prod t A
  T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_corrected_cycles B C C1 Prod t A T0 P Q N
  R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
≔ @one_cat_kernel_family_inclusion_reflect_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1
  R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R1 R2 m1) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1
  R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_left_cycle_lift B C C1 Prod t A
  T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_corrected_cycles B C C1 Prod t A T0 P Q N
  R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C)
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_left_cycle_lift B C C1 Prod t A
  T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)) (@Transf
  B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)) (λ v : τ
  (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)),
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1
  walking_arrow_src) v (@one_cat_middle_left_cycle_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R1 walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)))
  (@one_cat_row_triple_incoming_cycle_projection_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_sym _
  _ _ (@comp_assoc (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_left_cycle_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@eq_trans
  _ _ _ _ (@eq_ap (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1))
  (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)) (λ v : τ
  (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)), (@comp_fapp0 (Functor_cat
  B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R1 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t (@additive_terminal_object C Prod t A) R1) v)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@zero_cone_row_family_source_func B C t (@additive_terminal_object C Prod t A) R1)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_left_cycle_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_middle_corrected_left_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_left_cycle_reconstruction B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_middle_corrected_left_reconstruction B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2)))));

// The derived class cover cancels whole maps at its actual retained endpoints.
symbol one_cat_middle_class_cover_reflect_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  A) T0 P Q R2)) (Y : τ (Functor B C)) (u v : τ (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0)) (@one_cat_row_triple_outgoing_homology_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) Y)) (e : τ (@= (@Transf B C
  (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) Y)
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0)) (@one_cat_row_triple_outgoing_homology_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) Y u
  (@one_cat_middle_class_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0)) (@one_cat_row_triple_outgoing_homology_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) Y v
  (@one_cat_middle_class_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0)) (@one_cat_row_triple_outgoing_homology_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) Y) u v)
≔ @one_cat_homology_representative_reflect_path B C C1 Prod t A T0 P Q N (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0)) (@one_cat_row_triple_outgoing_homology_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@one_cat_row_triple_outgoing_homology_map B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2))) Y u v e;

// The derived boundary cover cancels whole maps at its actual retained endpoints.
symbol one_cat_middle_boundary_cover_reflect_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
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
  A) T0 P Q R2)) (Y : τ (Functor B C)) (u v : τ (@Transf B C (@one_cat_middle_class_cover_func B C C1 Prod t
  A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) Y)) (e : τ (@= (@Transf B C
  (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) Y)
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0
  m1 lower_zero E0 E1 E2) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) Y u (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C C1 Prod t A
  T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2) Y v (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0 R1
  R2 m0 m1 lower_zero E0 E1 E2))))
 : τ (@= (@Transf B C (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2) Y) u v)
≔ @one_cat_boundary_representative_reflect_path B C C1 Prod t A T0 P Q N (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_class_cycles B C C1 Prod t A T0 P
  Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_right_cycle_quotient_zero B C C1 Prod t A T0 P Q
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) Y u v e;

// The derived row cover cancels whole maps at its actual retained endpoints.
symbol one_cat_middle_row_cover_reflect_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  A) T0 P Q R2)) (Y : τ (Functor B C)) (u v : τ (@Transf B C (@one_cat_middle_boundary_cover_func B C C1
  Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) Y)) (e : τ (@= (@Transf B C
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) Y)
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) Y u (@one_cat_middle_row_cover_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P
  Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2) Y v (@one_cat_middle_row_cover_projection B C C1 Prod t A T0 P Q N R0 R1
  R2 m0 m1 lower_zero E0 E1 E2))))
 : τ (@= (@Transf B C (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) Y) u v)
≔ @one_cat_cospan_kernel_first_reflect_path B C C1 Prod t A T0 P Q N
  (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@one_cat_middle_right_boundary_representative B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_short_exact_outgoing_cokernel_zero B C C1 Prod t A T0 P Q (@zero_cone_row_family_source_func B C t
  (@additive_terminal_object C Prod t A) R0) (@zero_cone_row_family_diagram_func B C t (@additive_terminal_object
  C Prod t A) R0) (@one_cat_zero_cone_row_family_transf B C C1 t (@additive_terminal_object C Prod t A) R0) E0) Y
  u v e;
