/* Three original covers and a corrected cycle for middle homology exactness. */
require open emdash.emdash3_2_one_cat_boundary_representatives;
require open emdash.emdash3_2_one_cat_row_homology_zero_pairs;

// Cover the actual kernel of H(p) using the original middle homology quotient.
symbol one_cat_middle_class_cover_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
 : τ (Functor B C)
≔ @one_cat_homology_representative_func B C C1 Prod t A T0 P Q N (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
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
  E0 E1 E2)));

// The derived class-cover projection retains the original kernel of H(p).
symbol one_cat_middle_class_projection [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
 : τ (@Transf B C (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@one_cat_row_triple_outgoing_homology_map B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2))))
≔ @one_cat_homology_representative_projection B C C1 Prod t A T0 P Q N (@zero_cone_row_family_vertex_func B
  C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
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
  E0 E1 E2)));

// The whole cycle representative lands in the original middle cycle object.
symbol one_cat_middle_class_cycles [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
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
 : τ (@Transf B C (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)))
≔ @one_cat_homology_representative_cycles B C C1 Prod t A T0 P Q N (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
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
  E0 E1 E2)));

// The original middle quotient reconstructs the original kernel inclusion after this cover.
symbol one_cat_middle_class_reconstruction [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
 : τ (@= (@Transf B C (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2
  m1) (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero))) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
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
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero)) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
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
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@one_cat_middle_class_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero))
  (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@one_cat_middle_class_cycles B C C1
  Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
≔ @one_cat_homology_representative_path B C C1 Prod t A T0 P Q N (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
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
  E0 E1 E2)));

// The induced right cycle has zero original homology quotient, using the actual kernel condition.
symbol one_cat_middle_right_cycle_quotient_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
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
 : τ (@= (@Transf B C (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0))) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_class_cycles B C C1 Prod t A T0 P
  Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0))))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0)) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0)) (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_row_triple_outgoing_diagram_map B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2)) (@one_cat_middle_class_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0))) (@Transf B C (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0))) (λ w : τ (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0))), (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) w (@one_cat_middle_class_cycles B C C1 Prod t A T0 P Q N
  R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@kernel_adjunction_family_map_transf B C (@additive_preadditive
  C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_row_triple_outgoing_diagram_map B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@homology_adjunction_family_func B C (@additive_preadditive C
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
  E0 E1 E2) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero))) (@eq_sym _ _ _
  (@one_cat_row_triple_outgoing_homology_projection_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_sym
  _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2
  m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@homology_adjunction_family_func B C (@additive_preadditive C
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
  E0 E1 E2) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@one_cat_middle_class_cycles B C C1
  Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero))) (@Transf B C (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0))) (λ w : τ (@Transf B C (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero))), (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
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
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2) w)) (@comp_fapp0 (Functor_cat
  B C) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero)) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@one_cat_middle_class_cycles B C C1
  Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@one_cat_row_triple_outgoing_homology_map B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2))) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero))
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
  E0 E1 E2))) (@one_cat_middle_class_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2)) (@eq_sym _ _ _ (@one_cat_middle_class_reconstruction B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_middle_class_cover_func
  B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C
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
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
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
  E0 E1 E2))) (@one_cat_middle_class_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@homology_adjunction_family_func
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0)) (@one_cat_row_triple_outgoing_homology_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0))) (@Transf B C (@one_cat_middle_class_cover_func B C C1
  Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0))) (λ w : τ (@Transf B C (@kernel_adjunction_family_func B C
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
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0))), (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@one_cat_row_triple_outgoing_homology_map B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2))) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0)) w (@one_cat_middle_class_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
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
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
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
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
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
  E0 E1 E2)))) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@one_cat_row_triple_outgoing_homology_map B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2))) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0))) (@one_cat_kernel_family_annihilation_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero)) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0)) (@one_cat_row_triple_outgoing_homology_map B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))))
  (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0
  (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@one_cat_row_triple_outgoing_homology_map B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2))) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0)) (@one_cat_middle_class_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2))))))));

// The original right boundary quotient derives the second whole cover.
symbol one_cat_middle_boundary_cover_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
 : τ (Functor B C)
≔ @one_cat_boundary_representative_func B C C1 Prod t A T0 P Q N (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
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
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2);

// The second cover retains the original first-cover parameter object.
symbol one_cat_middle_boundary_projection [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
 : τ (@Transf B C (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
≔ @one_cat_boundary_representative_projection B C C1 Prod t A T0 P Q N (@zero_cone_row_family_vertex_func B
  C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
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
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2);

// The original right boundary representative lands in the original previous right object.
symbol one_cat_middle_right_boundary_representative [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
 : τ (@Transf B C (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt))
≔ @one_cat_boundary_representative_map B C C1 Prod t A T0 P Q N (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
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
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2);

// The original right boundary reconstructs the induced cycle after the second cover.
symbol one_cat_middle_boundary_reconstruction [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
 : τ (@= (@Transf B C (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1))) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C C1 Prod t
  A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@one_cat_middle_right_boundary_representative B C C1 Prod
  t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_class_cycles B C C1 Prod t A T0 P
  Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2)))
≔ @one_cat_boundary_representative_path B C C1 Prod t A T0 P Q N (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t
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
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2);

// The original outgoing row map gives the third difference-kernel parameter object.
symbol one_cat_middle_row_cover_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
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
 : τ (Functor B C)
≔ @one_cat_cospan_kernel_func B C C1 Prod t A T0 P Q (@one_cat_middle_boundary_cover_func B C C1 Prod
  t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@one_cat_middle_right_boundary_representative B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0);

// The third projection retains the actual boundary-cover object.
symbol one_cat_middle_row_cover_projection [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  E2) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
≔ @one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q (@one_cat_middle_boundary_cover_func B C C1 Prod
  t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@one_cat_middle_right_boundary_representative B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0);

// The whole row representative lands in the original previous middle object.
symbol one_cat_middle_row_representative [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src))
≔ @one_cat_cospan_kernel_second B C C1 Prod t A T0 P Q (@one_cat_middle_boundary_cover_func B C C1
  Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@one_cat_middle_right_boundary_representative B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0);

// The original row projection reconstructs the original right boundary representative.
symbol one_cat_middle_row_reconstruction [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_tgt) (@one_cat_middle_right_boundary_representative B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@one_cat_middle_row_cover_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P
  Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A)
  R0 walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_middle_row_representative B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
≔ @one_cat_cospan_kernel_compatibility B C C1 Prod t A T0 P Q (@one_cat_middle_boundary_cover_func B C
  C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@one_cat_middle_right_boundary_representative B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0);

// The lifted cycle and the original middle boundary have the same induced right cycle.
symbol one_cat_middle_cycle_boundary_correction_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
  E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)))
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
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_class_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_middle_row_cover_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
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
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2
  m1) (@one_cat_zero_cone_middle_column_input B C C1 t (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1
  lower_zero)) (@one_cat_middle_row_representative B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2))))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N
  R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2
  m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_class_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_middle_row_cover_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1))) (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0
  m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1))) (λ w : τ (@Transf B C (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1))), (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0
  P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) w (@one_cat_middle_row_cover_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C C1 Prod t A
  T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_class_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0
  m1 lower_zero E0 E1 E2) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_class_cover_func B C C1 Prod t A T0
  P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_class_cycles B C C1 Prod t A T0 P
  Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2)) (@comp_assoc (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C
  C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_middle_class_cover_func B C C1 Prod t A
  T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_class_cycles B C C1 Prod t A T0 P
  Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))) (@Transf B C
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))) (λ w : τ
  (@Transf B C (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))),
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) w (@one_cat_middle_row_cover_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C C1 Prod t A
  T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_class_cover_func B C C1 Prod t A T0
  P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_class_cycles B C C1 Prod t A T0 P
  Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C
  C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@one_cat_middle_right_boundary_representative B C C1 Prod
  t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@eq_sym _ _ _ (@one_cat_middle_boundary_reconstruction
  B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@one_cat_middle_right_boundary_representative B C C1 Prod
  t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_middle_row_cover_projection B C C1 Prod t A T0
  P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)) (@Transf
  B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))) (λ w : τ
  (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)),
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_tgt) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) w)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt)
  (@one_cat_middle_right_boundary_representative B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@one_cat_middle_row_cover_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_middle_row_representative B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_middle_row_reconstruction B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N
  R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t
  A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_tgt) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t
  A) R1 R2 m1) (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@zero_cone_row_family_outgoing B C
  t (@additive_terminal_object C Prod t A) R0) (@one_cat_middle_row_representative B C C1 Prod t A T0 P Q N
  R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))) (@Transf B C
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))) (λ w : τ
  (@Transf B C (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1))), (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0
  P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C
  Prod t A) R0 walking_arrow_src) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1)) w (@one_cat_middle_row_representative B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_zero_cone_right_column_input B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0)) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object
  C Prod t A) R0)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@kernel_adjunction_family_boundary_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero))) (@eq_sym _ _ _
  (@one_cat_homology_family_boundary_map_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  (@additive_terminal_object C Prod t A) R0 walking_arrow_tgt) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero) (@one_cat_zero_cone_right_column_input B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0) (@zero_cone_row_family_outgoing B C t (@additive_terminal_object C Prod t A) R0)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_row_triple_outgoing_map_path B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2)))) (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A
  T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object
  C Prod t A) R0 walking_arrow_src) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@kernel_adjunction_family_boundary_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@one_cat_middle_row_representative
  B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))))))))));

// The original whole difference produces the corrected middle cycle.
symbol one_cat_middle_corrected_cycles [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)))
≔ (@one_cat_difference_family B C C1 Prod t A T0 (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_class_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_middle_row_cover_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_boundary_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@one_cat_middle_row_representative
  B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)));

// Whole bilinearity and the proved correction relation annihilate the induced right cycle.
symbol one_cat_middle_corrected_right_cycles_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
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
  A) T0 P Q R2))
 : τ (@= (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)))
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
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_difference_family B C C1 Prod t A T0
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_class_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_middle_row_cover_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_boundary_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@one_cat_middle_row_representative
  B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1
  R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1))))
≔ @one_cat_difference_family_postcompose_zero_path B C C1 Prod t A T0 (@one_cat_middle_row_cover_func B C C1
  Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_right_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_class_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@one_cat_middle_row_cover_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@zero_cone_row_family_vertex_func B C t (@additive_terminal_object C Prod t A) R0
  walking_arrow_src) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) (@kernel_adjunction_family_boundary_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_row_family_vertex_func
  B C t (@additive_terminal_object C Prod t A) R0 walking_arrow_src) (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1) (@one_cat_zero_cone_middle_column_input B C C1 t
  (@additive_terminal_object C Prod t A) T0 R0 R1 R2 m0 m1 lower_zero)) (@one_cat_middle_row_representative
  B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@kernel_adjunction_family_map_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_right_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_outgoing_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_cycle_boundary_correction_path B
  C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2);
