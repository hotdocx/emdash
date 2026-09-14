require open emdash.emdash3_2_one_cat_middle_homology_cycles;

// The original induced left map recovers the constructed corrected cycle.
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
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R2)) ⊢
  (@one_cat_middle_left_cycle_map_path B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) : τ (@=
  (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_left_cycle_lift B C C1 Prod t A T0 P Q
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_corrected_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2));
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
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R2)) (x : τ (Obj B)) ⊢
  @eq_ap (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))) (Hom C
  (@fapp0 B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) x)
  (@fapp0 B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  x)) (λ h : τ (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))),
  (@tapp0_fapp0 B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)) x h))
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
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_left_cycle_lift B C C1 Prod t A T0 P Q
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_corrected_cycles B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) (@one_cat_middle_left_cycle_map_path B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2) : τ (@= (Hom C (@fapp0 B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) x) (@fapp0 B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) x)) (@tapp0_fapp0 B C (@one_cat_middle_row_cover_func B C C1
  Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) x (@comp_fapp0 (Functor_cat B C)
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@kernel_adjunction_family_map_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@zero_cone_middle_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1)
  (@one_cat_row_triple_incoming_diagram_map B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2)) (@one_cat_middle_left_cycle_lift B C C1 Prod t A T0 P Q
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) (@tapp0_fapp0 B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_middle_column_outgoing_func B C t
  (@additive_terminal_object C Prod t A) R1 R2 m1)) x (@one_cat_middle_corrected_cycles B C C1 Prod t A T0 P Q N
  R0 R1 R2 m0 m1 lower_zero E0 E1 E2)));

// The whole left-cycle lift remains an arrow with generic Hom action.
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
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R2)) (X : τ (Functor B C))
  ⊢ @hom_postcomp_func (Functor_cat B C) (Functor_cat B C) (@id_func (Functor_cat B C)) X
  (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object C Prod t A) R1 R2 m1))
  (@one_cat_middle_left_cycle_lift B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) : τ (Functor
  (@Transf_cat B C X (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
  (@Transf_cat B C X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@zero_cone_left_column_outgoing_func B C t (@additive_terminal_object
  C Prod t A) R1 R2 m1))));

// Original class cover cancellation needs no extra cover premise.
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
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R2)) (Y : τ (Functor B C))
  (u v : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
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
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) Y)) (e : τ (@= (@Transf B C
  (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) Y) (@comp_fapp0
  (Functor_cat B C) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)
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
  E0 E1 E2))) Y u (@one_cat_middle_class_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2))
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
  (@one_cat_middle_class_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2)))) ⊢
  @one_cat_middle_class_cover_reflect_path B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2 Y u v e : τ
  (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
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
  (@additive_terminal_object C Prod t A) T0 P Q R0 R1 R2 m0 m1 lower_zero E0 E1 E2))) Y) u v);

// Original boundary cover cancellation needs no extra cover premise.
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
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R2)) (Y : τ (Functor B C))
  (u v : τ (@Transf B C (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0 E1
  E2) Y)) (e : τ (@= (@Transf B C (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) Y) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P
  Q N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0
  m1 lower_zero E0 E1 E2) Y u (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q
  N R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) Y v (@one_cat_middle_boundary_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero
  E0 E1 E2)))) ⊢ @one_cat_middle_boundary_cover_reflect_path B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2 Y u v e : τ (@= (@Transf B C (@one_cat_middle_class_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) Y) u v);

// Original row cover cancellation needs no extra cover premise.
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
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q R2)) (Y : τ (Functor B C))
  (u v : τ (@Transf B C (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1 lower_zero E0
  E1 E2) Y)) (e : τ (@= (@Transf B C (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) Y) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N
  R0 R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) Y u (@one_cat_middle_row_cover_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2)) (@comp_fapp0 (Functor_cat B C) (@one_cat_middle_row_cover_func B C C1 Prod t A T0 P Q N R0
  R1 R2 m0 m1 lower_zero E0 E1 E2) (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2) Y v (@one_cat_middle_row_cover_projection B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2)))) ⊢ @one_cat_middle_row_cover_reflect_path B C C1 Prod t A T0 P Q N R0 R1 R2 m0 m1
  lower_zero E0 E1 E2 Y u v e : τ (@= (@Transf B C (@one_cat_middle_boundary_cover_func B C C1 Prod t A T0 P Q N
  R0 R1 R2 m0 m1 lower_zero E0 E1 E2) Y) u v);
