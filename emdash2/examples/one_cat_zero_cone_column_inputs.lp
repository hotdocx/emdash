/* Whole native row action supplies the squares and column-zero data. */
require open emdash.emdash3_2_one_cat_zero_cone_column_inputs;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (R S : τ
  (Functor B (@ZeroArrowCone_cat C t T))) (m : τ (@Transf B (@ZeroArrowCone_cat C t T) R S))
  ⊢ (@one_cat_zero_cone_row_incoming_square_path B C C1 t T R S m) : τ (@= (@Transf B C
    (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src))
    (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_vertex_func B
    C t T R walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1
    t T R)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R)
    (@zero_cone_row_family_source_func B C t T S) (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)
    (@one_cat_zero_cone_row_family_incoming B C C1 t T S) (@zero_cone_row_family_source_map B C t T R S m)));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (R S : τ
  (Functor B (@ZeroArrowCone_cat C t T))) (m : τ (@Transf B (@ZeroArrowCone_cat C t T) R S))
  ⊢ (@one_cat_zero_cone_row_outgoing_square_path B C C1 t T R S m) : τ (@= (@Transf B C
    (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T S
    walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T S
    walking_arrow_tgt) (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_tgt)
    (@zero_cone_row_family_outgoing B C t T R)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C
    t T R walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T S walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T S)
    (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_src)));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (R S : τ
  (Functor B (@ZeroArrowCone_cat C t T))) (m : τ (@Transf B (@ZeroArrowCone_cat C t T) R S)) (x : τ (Obj B))
  ⊢ (@tapp0_fapp0 B C (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_source_func B C t T S) x
    (@zero_cone_row_family_source_map B C t T R S m)) ≡ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 B (@ZeroArrowCone_cat C t T) R x) (@fapp0 B (@ZeroArrowCone_cat C t T)
    S x) (@tapp0_fapp0 B (@ZeroArrowCone_cat C t T) R S x m));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (R S : τ
  (Functor B (@ZeroArrowCone_cat C t T))) (m : τ (@Transf B (@ZeroArrowCone_cat C t T) R S)) (x : τ (Obj B))
  ⊢ (@tapp0_fapp0 B C (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src) x (@zero_cone_row_family_vertex_map B C t T R S m
    walking_arrow_src)) ≡ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_src) (@fapp0 B (@ZeroArrowCone_cat C t T) R x) (@fapp0 B (@ZeroArrowCone_cat C t T) S x)
    (@tapp0_fapp0 B (@ZeroArrowCone_cat C t T) R S x m));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T)))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (z : τ
    (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0
    R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
  ⊢ (@one_cat_zero_cone_left_column_zero_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E2) : τ (@= (@Transf B C
    (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R2)) (@comp_fapp0
    (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R1)
    (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_source_map B C t T R1 R2 m1)
    (@zero_cone_row_family_source_map B C t T R0 R1 m0)) (@zero_arrow_family_zero_transf B C t T T0
    (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R2)));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T)))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (z : τ
    (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0
    R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
  ⊢ (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E2) : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
    (@zero_cone_row_family_source_func B C t T R0)) (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T)))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (z : τ
    (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0
    R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2))
  ⊢ (@one_cat_kernel_family_input_incoming_path B C C1 t T T0 (@zero_cone_row_family_source_func B C t T R0)
    (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_row_family_source_map B C t T R0 R1 m0)
    (@one_cat_zero_cone_left_column_zero_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E2)) : τ (@= (@Transf B C
    (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R1))
    (@zero_arrow_family_incoming_transf B C t T (@zero_cone_row_family_source_func B C t T R0)
    (@zero_cone_left_column_outgoing_func B C t T R1 R2 m1) (@one_cat_zero_cone_left_column_input B C Add C1 t T T0 P
    Q R0 R1 R2 m0 m1 z E2)) (@zero_cone_row_family_source_map B C t T R0 R1 m0));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T)))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (z : τ
    (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0
    R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0))
  ⊢ (@one_cat_zero_cone_right_column_zero_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E0) : τ (@= (@Transf B C
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R2
    walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt) (@zero_cone_row_family_vertex_map B C t T R1 R2
    m1 walking_arrow_tgt) (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_tgt))
    (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_tgt)));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T)))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (z : τ
    (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0
    R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0))
  ⊢ (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E0) : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)) (@zero_cone_right_column_outgoing_func B C t T
    R1 R2 m1));

assert [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T)))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (z : τ
    (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0
    R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E0 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R0))
  ⊢ (@one_cat_kernel_family_input_incoming_path B C C1 t T T0 (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1 R2 m1) (@zero_cone_row_family_vertex_map B C
    t T R0 R1 m0 walking_arrow_tgt) (@one_cat_zero_cone_right_column_zero_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z
    E0)) : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt)
    (@zero_cone_row_family_vertex_func B C t T R1 walking_arrow_tgt)) (@zero_arrow_family_incoming_transf B C t T
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B C t T R1
    R2 m1) (@one_cat_zero_cone_right_column_input B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E0))
    (@zero_cone_row_family_vertex_map B C t T R0 R1 m0 walking_arrow_tgt));

assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (R S : τ
  (Functor B (@ZeroArrowCone_cat C t T))) (m : τ (@Transf B (@ZeroArrowCone_cat C t T) R S)) (m2 : τ (@Transf B
  (@ZeroArrowCone_cat C t T) R S))
  ⊢ (@zero_cone_row_family_source_map B C t T R S m) ≡ (@zero_cone_row_family_source_map B C t T R S m2);

assertnot [B C : Cat] [Add : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C Add t T)) (Q : τ (@CokernelAdjunctionStructure C Add t T0))
  (R0 R1 R2 : τ (Functor B (@ZeroArrowCone_cat C t T)))
  (m0 : τ (@Transf B (@ZeroArrowCone_cat C t T) R0 R1)) (m1 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2)) (z : τ
    (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R1
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)
    (@zero_cone_row_family_vertex_map B C t T R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R0
    R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B C t T T0 (@zero_cone_row_family_vertex_func B C t T R0
    walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R2 walking_arrow_src)))) (E2 : τ
    (@OneCatZeroConeShortExactFamily B C Add C1 t T T0 P Q R2)) (m2 : τ (@Transf B (@ZeroArrowCone_cat C t T) R1 R2))
  ⊢ (@one_cat_zero_cone_left_column_zero_path B C Add C1 t T T0 P Q R0 R1 R2 m0 m1 z E2) : τ (@= (@Transf B C
    (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R2)) (@comp_fapp0
    (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R1)
    (@zero_cone_row_family_source_func B C t T R2) (@zero_cone_row_family_source_map B C t T R1 R2 m2)
    (@zero_cone_row_family_source_map B C t T R0 R1 m0)) (@zero_arrow_family_zero_transf B C t T T0
    (@zero_cone_row_family_source_func B C t T R0) (@zero_cone_row_family_source_func B C t T R2)));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (X : τ
  (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat
  C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D))
  ⊢ (@one_cat_native_incoming_parent_path B C C1 t T X D h) : τ (@= (@Transf B C X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src)) (@zero_arrow_family_incoming_transf B C t T X D h)
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) X) D h walking_arrow_src));

assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (X : τ
  (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h h2 : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
  D))
  ⊢ (@eq_refl (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) X) D h walking_arrow_src)) : τ (@= (@Transf B C X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
    (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D h walking_arrow_src)
    (@zero_arrow_family_incoming_transf B C t T X D h2));

assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (X : τ
  (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat
  C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D))
  ⊢ (@zero_arrow_family_incoming_transf B C t T X D h) ≡ (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D h
    walking_arrow_src);
