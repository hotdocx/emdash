/* Whole row observations on the original native ZeroArrowCone category.
   The original row functor precedes K/Q and carries every parameter action. */
require open emdash.emdash3_2_one_cat_family_naturality_paths;
require open emdash.emdash3_2_one_cat_zero_cones;
require open emdash.emdash3_2_one_cat_short_exact_family_cancellation;

// The first vertex and outgoing diagram of the original row family.
symbol zero_cone_row_family_source_func [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (R : τ
  (Functor B (@ZeroArrowCone_cat C t T)))
  : τ (Functor B C) ≔ @comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) R;
symbol zero_cone_row_family_diagram_func [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (R : τ
  (Functor B (@ZeroArrowCone_cat C t T)))
  : τ (Functor B (Functor_cat WalkingArrow_cat C)) ≔ @comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) R;
symbol zero_cone_row_family_vertex_func [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (R : τ
  (Functor B (@ZeroArrowCone_cat C t T))) (i : τ (Obj WalkingArrow_cat))
  : τ (Functor B C) ≔ @diagram_family_at_func B WalkingArrow_cat C (@zero_cone_row_family_diagram_func B C t T
    R) i;

// Restrict the existing whole universal zero-cone transformation.
symbol one_cat_zero_cone_row_family_transf [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (R : τ (Functor B (@ZeroArrowCone_cat C t T)))
  : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) (@zero_cone_row_family_source_func B C t T R))
    (@zero_cone_row_family_diagram_func B C t T R))
≔ @fapp0 _ _ (@comp_cat_con_fapp1_func B (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) R
  (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@zero_arrow_cone_first_func C t T)) (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_cone_universal_transf C C1
  t T);

// Original incoming and outgoing row transformations.
symbol one_cat_zero_cone_row_family_incoming [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (R : τ (Functor B (@ZeroArrowCone_cat C t T)))
  : τ (@Transf B C (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_vertex_func B C t
    T R walking_arrow_src))
≔ @zero_arrow_family_incoming_transf B C t T (@zero_cone_row_family_source_func B C t T R)
  (@zero_cone_row_family_diagram_func B C t T R) (@one_cat_zero_cone_row_family_transf B C C1 t T R);
symbol zero_cone_row_family_outgoing [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (R : τ (Functor B
  (@ZeroArrowCone_cat C t T)))
  : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R walking_arrow_tgt))
≔ @diagram_family_transf B WalkingArrow_cat C (@zero_cone_row_family_diagram_func B C t T R) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator;

// All vertex maps are native action of their original postcomposition functors.
symbol zero_cone_row_family_source_map [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (R S : τ
  (Functor B (@ZeroArrowCone_cat C t T))) (m : τ (@Transf B (@ZeroArrowCone_cat C t T) R S))
  : τ (@Transf B C (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_source_func B C t
    T S)) ≔ (@fapp1_fapp0 (Functor_cat B (@ZeroArrowCone_cat C t T)) (Functor_cat B C) (@comp_cat_cov_func B
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)) R S m);
symbol zero_cone_row_family_vertex_map [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (R S : τ
  (Functor B (@ZeroArrowCone_cat C t T))) (m : τ (@Transf B (@ZeroArrowCone_cat C t T) R S)) (i : τ (Obj
  WalkingArrow_cat))
  : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T R i) (@zero_cone_row_family_vertex_func B C
    t T S i)) ≔ (@fapp1_fapp0 (Functor_cat B (@ZeroArrowCone_cat C t T)) (Functor_cat B C) (@comp_cat_cov_func B
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T i)) R S m);

// E₀ of the restricted whole zero datum is the restricted original incoming map.
symbol one_cat_zero_cone_row_incoming_whisker_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ
  (Obj C)] (T : τ (@TerminalObject C t)) (R : τ (Functor B (@ZeroArrowCone_cat C t T)))
  : τ (@= (@Transf B C (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_vertex_func B
    C t T R walking_arrow_src)) (@one_cat_zero_cone_row_family_incoming B C C1 t T R) (@fapp0 _ _
    (@comp_cat_con_fapp1_func B (@ZeroArrowCone_cat C t T) C R (@zero_arrow_cone_first_func C t T)
    (@zero_arrow_cone_vertex_func C t T walking_arrow_src)) (@zero_arrow_family_incoming_transf (@ZeroArrowCone_cat C
    t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T))))
≔ @one_cat_diagram_family_whiskering_path (@ZeroArrowCone_cat C t T) B WalkingArrow_cat C C1
    (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
      T) (@zero_arrow_cone_first_func C t T)) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf
      C C1 t T) R walking_arrow_src;

// The outgoing observation likewise retains the original row functor.
symbol one_cat_zero_cone_row_outgoing_whisker_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ
  (Obj C)] (T : τ (@TerminalObject C t)) (R : τ (Functor B (@ZeroArrowCone_cat C t T)))
  : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T R walking_arrow_tgt)) (@zero_cone_row_family_outgoing B C t
    T R) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (@ZeroArrowCone_cat C t T) C R (@zero_arrow_cone_vertex_func C t T
    walking_arrow_src) (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)) (@zero_arrow_cone_differential_transf C
    t T)))
≔ @one_cat_diagram_family_transf_reindex_path B (@ZeroArrowCone_cat C t T) WalkingArrow_cat C C1
  (@zero_arrow_cone_diagram_func C t T) R
    walking_arrow_src walking_arrow_tgt walking_arrow_generator;

// The incoming row square is whole naturality, with no caller square field.
symbol one_cat_zero_cone_row_incoming_square_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ
  (Obj C)] (T : τ (@TerminalObject C t)) (R S : τ (Functor B (@ZeroArrowCone_cat C t T))) (m : τ (@Transf B
  (@ZeroArrowCone_cat C t T) R S))
  : τ (@= (@Transf B C (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_vertex_func B
    C t T S walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R)
    (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src) (@zero_cone_row_family_vertex_func B C
    t T S walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_src)
    (@one_cat_zero_cone_row_family_incoming B C C1 t T R)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_source_func B C t T S)
    (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)
    (@one_cat_zero_cone_row_family_incoming B C C1 t T S) (@zero_cone_row_family_source_map B C t T R S
    m)))
≔ @eq_trans (@Transf B C (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_vertex_func
  B C t T S walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R)
  (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  T S walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming B C C1 t T R)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_vertex_func B C t T R
  walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)
  (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_src) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (@ZeroArrowCone_cat C t T) C R (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_vertex_func C t T
  walking_arrow_src)) (@zero_arrow_family_incoming_transf (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t
  T)))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R)
  (@zero_cone_row_family_source_func B C t T S) (@zero_cone_row_family_vertex_func B C t T S
  walking_arrow_src) (@one_cat_zero_cone_row_family_incoming B C C1 t T S)
  (@zero_cone_row_family_source_map B C t T R S m))
    (@eq_ap (@Transf B C (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_vertex_func
      B C t T R walking_arrow_src)) (@Transf B C (@zero_cone_row_family_source_func B C t T R)
      (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)) (λ z : τ (@Transf B C
      (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_vertex_func B C t T R
      walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R)
      (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src) (@zero_cone_row_family_vertex_func B
      C t T S walking_arrow_src) (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_src) z))
      (@one_cat_zero_cone_row_family_incoming B C C1 t T R) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
      (@ZeroArrowCone_cat C t T) C R (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_vertex_func C t T
      walking_arrow_src)) (@zero_arrow_family_incoming_transf (@ZeroArrowCone_cat C t T) C t T
      (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
      C1 t T))) (@one_cat_zero_cone_row_incoming_whisker_path B C C1 t T R))
    (@eq_trans (@Transf B C (@zero_cone_row_family_source_func B C t T R)
      (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_vertex_func B C t T R
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)
      (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_src) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
      (@ZeroArrowCone_cat C t T) C R (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_vertex_func C t T
      walking_arrow_src)) (@zero_arrow_family_incoming_transf (@ZeroArrowCone_cat C t T) C t T
      (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
      C1 t T)))) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_source_func B C t T R)
      (@zero_cone_row_family_source_func B C t T S) (@zero_cone_row_family_vertex_func B C t T S
      walking_arrow_src) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (@ZeroArrowCone_cat C t T) C S
      (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_vertex_func C t T walking_arrow_src))
      (@zero_arrow_family_incoming_transf (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
      (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)))
      (@zero_cone_row_family_source_map B C t T R S m)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_source_func B C t T S)
      (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)
      (@one_cat_zero_cone_row_family_incoming B C C1 t T S) (@zero_cone_row_family_source_map B C t T R S
      m))
      (@one_cat_family_naturality_path B (@ZeroArrowCone_cat C t T) C C1 (@zero_arrow_cone_first_func C t T)
        (@zero_arrow_cone_vertex_func C t T walking_arrow_src) (@zero_arrow_family_incoming_transf (@ZeroArrowCone_cat
        C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
        (@zero_arrow_cone_universal_transf C C1 t T)) R S m)
      (@eq_ap (@Transf B C (@zero_cone_row_family_source_func B C t T S)
        (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)) (@Transf B C
        (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_vertex_func B C t T S
        walking_arrow_src)) (λ z : τ (@Transf B C (@zero_cone_row_family_source_func B C t T S)
        (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
        (@zero_cone_row_family_source_func B C t T R) (@zero_cone_row_family_source_func B C t T S)
        (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src) z
        (@zero_cone_row_family_source_map B C t T R S m))) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
        (@ZeroArrowCone_cat C t T) C S (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_vertex_func C t T
        walking_arrow_src)) (@zero_arrow_family_incoming_transf (@ZeroArrowCone_cat C t T) C t T
        (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
        C1 t T))) (@one_cat_zero_cone_row_family_incoming B C C1 t T S) (@eq_sym (@Transf B C
        (@zero_cone_row_family_source_func B C t T S) (@zero_cone_row_family_vertex_func B C t T S
        walking_arrow_src)) (@one_cat_zero_cone_row_family_incoming B C C1 t T S) (@fapp0 _ _
        (@comp_cat_con_fapp1_func B (@ZeroArrowCone_cat C t T) C S (@zero_arrow_cone_first_func C t T)
        (@zero_arrow_cone_vertex_func C t T walking_arrow_src)) (@zero_arrow_family_incoming_transf
        (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
        (@zero_arrow_cone_universal_transf C C1 t T))) (@one_cat_zero_cone_row_incoming_whisker_path B C C1 t T
        S))));

// The outgoing row square is whole naturality, with no caller square field.
symbol one_cat_zero_cone_row_outgoing_square_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ
  (Obj C)] (T : τ (@TerminalObject C t)) (R S : τ (Functor B (@ZeroArrowCone_cat C t T))) (m : τ (@Transf B
  (@ZeroArrowCone_cat C t T) R S))
  : τ (@= (@Transf B C (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T S walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
    (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src) (@zero_cone_row_family_vertex_func B C
    t T R walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T S walking_arrow_tgt)
    (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_tgt) (@zero_cone_row_family_outgoing B C
    t T R)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
    (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src) (@zero_cone_row_family_vertex_func B C
    t T S walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T S) (@zero_cone_row_family_vertex_map
    B C t T R S m walking_arrow_src)))
≔ @eq_trans (@Transf B C (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T S walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
  (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  T R walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T S walking_arrow_tgt)
  (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t
  T R)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T R walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t
  T S walking_arrow_tgt) (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_tgt) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (@ZeroArrowCone_cat C t T) C R (@zero_arrow_cone_vertex_func C t T walking_arrow_src)
  (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)) (@zero_arrow_cone_differential_transf C t T))) (@comp_fapp0
  (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
  (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src) (@zero_cone_row_family_vertex_func B C t
  T S walking_arrow_tgt) (@zero_cone_row_family_outgoing B C t T S) (@zero_cone_row_family_vertex_map B C
  t T R S m walking_arrow_src))
    (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R walking_arrow_tgt)) (@Transf B C
      (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src) (@zero_cone_row_family_vertex_func B
      C t T S walking_arrow_tgt)) (λ z : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T R
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T R walking_arrow_tgt)), (@comp_fapp0
      (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T R walking_arrow_tgt) (@zero_cone_row_family_vertex_func B
      C t T S walking_arrow_tgt) (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_tgt) z))
      (@zero_cone_row_family_outgoing B C t T R) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (@ZeroArrowCone_cat C t
      T) C R (@zero_arrow_cone_vertex_func C t T walking_arrow_src) (@zero_arrow_cone_vertex_func C t T
      walking_arrow_tgt)) (@zero_arrow_cone_differential_transf C t T))
      (@one_cat_zero_cone_row_outgoing_whisker_path B C C1 t T R))
    (@eq_trans (@Transf B C (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T S walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
      (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src) (@zero_cone_row_family_vertex_func B
      C t T R walking_arrow_tgt) (@zero_cone_row_family_vertex_func B C t T S walking_arrow_tgt)
      (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
      (@ZeroArrowCone_cat C t T) C R (@zero_arrow_cone_vertex_func C t T walking_arrow_src)
      (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)) (@zero_arrow_cone_differential_transf C t T)))
      (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src) (@zero_cone_row_family_vertex_func B
      C t T S walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (@ZeroArrowCone_cat C t T) C S
      (@zero_arrow_cone_vertex_func C t T walking_arrow_src) (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt))
      (@zero_arrow_cone_differential_transf C t T)) (@zero_cone_row_family_vertex_map B C t T R S m
      walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R
      walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)
      (@zero_cone_row_family_vertex_func B C t T S walking_arrow_tgt) (@zero_cone_row_family_outgoing B C
      t T S) (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_src))
      (@one_cat_family_naturality_path B (@ZeroArrowCone_cat C t T) C C1 (@zero_arrow_cone_vertex_func C t T
        walking_arrow_src) (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
        (@zero_arrow_cone_differential_transf C t T) R S m)
      (@eq_ap (@Transf B C (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)
        (@zero_cone_row_family_vertex_func B C t T S walking_arrow_tgt)) (@Transf B C
        (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src) (@zero_cone_row_family_vertex_func
        B C t T S walking_arrow_tgt)) (λ z : τ (@Transf B C (@zero_cone_row_family_vertex_func B C t T S
        walking_arrow_src) (@zero_cone_row_family_vertex_func B C t T S walking_arrow_tgt)), (@comp_fapp0
        (Functor_cat B C) (@zero_cone_row_family_vertex_func B C t T R walking_arrow_src)
        (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src) (@zero_cone_row_family_vertex_func
        B C t T S walking_arrow_tgt) z (@zero_cone_row_family_vertex_map B C t T R S m walking_arrow_src)))
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B (@ZeroArrowCone_cat C t T) C S (@zero_arrow_cone_vertex_func C t T
        walking_arrow_src) (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt))
        (@zero_arrow_cone_differential_transf C t T)) (@zero_cone_row_family_outgoing B C t T S) (@eq_sym
        (@Transf B C (@zero_cone_row_family_vertex_func B C t T S walking_arrow_src)
        (@zero_cone_row_family_vertex_func B C t T S walking_arrow_tgt)) (@zero_cone_row_family_outgoing B
        C t T S) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (@ZeroArrowCone_cat C t T) C S (@zero_arrow_cone_vertex_func
        C t T walking_arrow_src) (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt))
        (@zero_arrow_cone_differential_transf C t T)) (@one_cat_zero_cone_row_outgoing_whisker_path B C C1 t T
        S))));

// Whole short-exactness at the actual maps of the original row functor.
symbol OneCatZeroConeShortExactFamily [B C : Cat] [Add : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C Add t T))
  (Q : τ (@CokernelAdjunctionStructure C Add t T0)) (R : τ (Functor B (@ZeroArrowCone_cat C t T))) : Grpd
≔ @OneCatShortExactFamily B C Add C1 t T T0 P Q (@zero_cone_row_family_source_func B C t T R)
  (@zero_cone_row_family_diagram_func B C t T R) (@one_cat_zero_cone_row_family_transf B C C1 t T R);
