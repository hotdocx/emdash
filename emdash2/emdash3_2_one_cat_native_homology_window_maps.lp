/* Four-row native window assembly with the original row functors and maps.
   The two middle-chain laws are whole mathematical input. Every other
   column law and commuting square is derived; no pointwise naturality
   field or old PreAbelianCategory dictionary enters this interface.
   E0 is retained for the forthcoming cover-epicity proof. */
require open emdash.emdash3_2_one_cat_homology_covered_maps;

// The original upper triple gives the right-column homology input.
symbol one_cat_native_window_right_column_input [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
    T T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@= (@Transf B C
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C
    t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B
    C Add C1 t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
  : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_tgt))
    (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0))
≔ @one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q Rm R0 R1 mm m0 upper_zero Em;

// The original lower triple gives the left-column homology input.
symbol one_cat_native_window_left_column_input [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
    T T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@= (@Transf B C
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C
    t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B
    C Add C1 t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
  : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) (@zero_cone_row_family_source_func B C t T R0))
    (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1))
≔ @one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E2;

// Source and target H are the original constructions at those actual inputs.
symbol one_cat_native_window_source_homology_func [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
    T T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@= (@Transf B C
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C
    t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B
    C Add C1 t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) : τ (Functor B
    C)
≔ @homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@one_cat_native_window_right_column_input B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2);
symbol one_cat_native_window_target_homology_func [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
    T T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@= (@Transf B C
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C
    t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B
    C Add C1 t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) : τ (Functor B
    C)
≔ @homology_adjunction_family_func B C Add t T T0 P Q (@zero_cone_row_family_source_func B C t T R0)
  (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_native_window_left_column_input B C
  Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2);

// The canonical map ρ retains the original right H and the literal kernel pullback.
symbol one_cat_native_window_cover_transf [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
    T T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@= (@Transf B C
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C
    t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B
    C Add C1 t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) : τ (@Transf B
    C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@zero_cone_row_family_outgoing B C t T R0)) (@one_cat_native_window_source_homology_func B C Add C1 t
    T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
≔ @one_cat_homology_cover_transf B C Add C1 t T T0 P Q (@zero_cone_row_family_vertex_func B C t T Rm
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
  (@one_cat_native_window_right_column_input B C Add C1 t T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em
  E0 E1 E2) (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
  (@zero_cone_row_family_outgoing B C t T R0);

// θ shares that exact source and lands in the original left H.
symbol one_cat_native_window_covered_transf [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (Rm R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T))) (mm : τ (@Transf B (@ZeroArrowCone_cat C t T) Rm R0))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  (upper_zero : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf B C t
    T T0 (@zero_cone_row_family_vertex_func B C t T Rm walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)))) (lower_zero : τ (@= (@Transf B C
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
    C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src) (@zero_cone_row_family_vertex_map B C
    t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_src))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src))))
  (Em : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q Rm)) (E0 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0)) (E1 : τ (@OneCatZeroConeShortExactFamily B
    C Add C1 t T T0 P Q R1)) (E2 : τ (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) : τ (@Transf B
    C (@kernel_precomposition_family_func B C Add t T P (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_right_column_outgoing_func B C t T R0 R1 m0)
    (@zero_cone_row_family_outgoing B C t T R0)) (@one_cat_native_window_target_homology_func B C Add C1 t
    T T0 P Q Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
≔ @one_cat_native_covered_homology_transf B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 lower_zero E1 E2;
