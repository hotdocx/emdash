/* Whole cokernel target observation at the original diagram family.
   This is the dual ambient observation required by row cancellation and ρ. */
require open emdash.emdash3_2_one_cat_cokernel_family_descent;
require open emdash.emdash3_2_one_cat_whiskering_paths;
require open emdash.emdash3_2_image_coimage_adjunction_families;

// E₁ commutes with restricting the original whole unit.
symbol one_cat_cokernel_family_unit_target_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (@sym_transf_tapp0_transf B
    WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (@fapp0 _ _
    (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) D (@id_func
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 Q)))
    (@unit_adj_transf (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q))) walking_arrow_tgt) (@fapp0 _ _
    (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 Q)) (@cokernel_adjunction_projection C S t T0 Q)))
≔ @one_cat_whiskering_path (Functor_cat WalkingArrow_cat C) B (Functor_cat WalkingArrow_cat C) C
  (@one_cat_functor_category WalkingArrow_cat C C1) C1 D
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@id_func (Functor_cat WalkingArrow_cat C))
      (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 Q)) (@unit_adj_transf (Functor_cat
      WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_evidence C S t T0 Q));

// The graph restriction and raw whiskering retain the same original q.
symbol one_cat_cokernel_family_projection_whisker_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D))
    (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
    (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
    (@cokernel_adjunction_func C S t T0 Q)) (@cokernel_adjunction_projection C S t T0 Q)))
≔ @one_cat_diagram_family_transf_reindex_path B (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C C1
    (@cokernel_adjunction_arrow_func C S t T0 Q) D walking_arrow_src walking_arrow_tgt walking_arrow_generator;

// Native E₁ after transpose is a whole internal Hom functor.
symbol one_cat_cokernel_family_projection_func [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C))
  : τ (Functor (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat
    (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) D) (@fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt)
    (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y))))
≔ @comp_cat_fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0))
  Y)) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) D) (@fapp0 (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt)
  (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y)))
    (@fapp1_func (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
      WalkingArrow_cat C walking_arrow_tgt) D (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat
      C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y))
      (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
      WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_evidence C S t T0 Q) D Y);

// Keeping native Hom annotations literal lets the composite application compute.
symbol one_cat_cokernel_family_projection_beta [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C)) (v : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t
    T0 Q) D) Y))
  : τ (@= (Obj (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) D) (@fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt)
    (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y)))) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B C) (@fapp0
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
    WalkingArrow_cat C walking_arrow_tgt) D) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
    C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) (@fapp0 (Functor_cat B C) (Functor_cat
    B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0)) Y))) (@one_cat_cokernel_family_projection_func B C S C1 t T0 Q D Y) v)
    (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t
    T0)) Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
    C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t
    T0)) Y)) (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) v) walking_arrow_tgt))
≔ @eq_refl (Obj (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) D) (@fapp0 (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt)
  (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y)))) (@sym_transf_tapp0_transf B WalkingArrow_cat C D
  (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat
  B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0
  (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y)) (@one_cat_adjunction_family_transpose_func B
  (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C
  S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) v)
  walking_arrow_tgt);

// Read E₁(transpose(v)) as v∘q_D through the original unit.
symbol one_cat_cokernel_family_projection_raw_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C)) (v : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t
    T0 Q) D) Y))
  : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@sym_transf_tapp0_transf
    B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
    Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t
    T0)) Y)) (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) v) walking_arrow_tgt)
    (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0
    B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v (@fapp0 _ _
    (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 Q)) (@cokernel_adjunction_projection C S t T0 Q))))
≔ let u : τ (@Transf B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D))) ≔ (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat
  C) (Functor_cat WalkingArrow_cat C) D (@id_func (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat
  WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
  (@cokernel_adjunction_func C S t T0 Q))) (@unit_adj_transf (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0
  Q))) in
  let iv : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) D)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) Y)) ≔ (@fapp0 _ _ (@comp_cat_cov_fapp1_func B C (Functor_cat WalkingArrow_cat
    C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) D) Y) v) in
  let u1 : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) ≔ (@sym_transf_tapp0_transf B
    WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) u
    walking_arrow_tgt) in
  let iv1 : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0
    Q) D) Y) ≔ (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) D)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) Y) iv walking_arrow_tgt) in
  @eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)
    (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0
    (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y)) (@one_cat_adjunction_family_transpose_func B
    (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func
    C S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) v)
    walking_arrow_tgt) (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) (@comp_fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (@comp_cat_fapp0
    B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) iv u) walking_arrow_tgt) (@comp_fapp0
    (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v (@fapp0 _ _
    (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 Q)) (@cokernel_adjunction_projection C S t T0 Q)))
    (@eq_ap (@Transf B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) Y)) (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_tgt) Y) (λ h : τ (@Transf B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat
      WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y)), (@sym_transf_tapp0_transf B WalkingArrow_cat C D
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) h
      walking_arrow_tgt)) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0
      Q)) D) Y) (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0 (Functor_cat B C) (Functor_cat B
      (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0)) Y)) (@one_cat_adjunction_family_transpose_func B (Functor_cat
      WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0
      Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) v) (@comp_fapp0
      (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
      (@cokernel_adjunction_func C S t T0 Q) D)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) Y) iv u) (@one_cat_adjunction_family_transpose_agrees B (Functor_cat
      WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0
      Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y v))
    (@eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) Y) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) D
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B
      (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (@comp_cat_fapp0 B C (Functor_cat
      WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) iv u) walking_arrow_tgt) (@comp_fapp0 (Functor_cat B
      C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
      WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y iv1 u1) (@comp_fapp0 (Functor_cat B C)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
      WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v (@fapp0 _ _ (@comp_cat_con_fapp1_func B
      (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
      (@cokernel_adjunction_func C S t T0 Q)) (@cokernel_adjunction_projection C S t T0 Q)))
      (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_tgt D (@comp_cat_fapp0 B C
        (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat
        WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (@comp_cat_fapp0 B C (Functor_cat
        WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) iv u)
      (@eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@comp_fapp0
        (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
        (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y iv1 u1) (@comp_fapp0
        (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
        (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v u1) (@comp_fapp0 (Functor_cat
        B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
        WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v (@fapp0 _ _ (@comp_cat_con_fapp1_func B
        (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
        (@cokernel_adjunction_func C S t T0 Q)) (@cokernel_adjunction_projection C S t T0 Q)))
        (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0
          Q) D) Y) (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (λ z : τ
          (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)
          Y), (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
          (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y z u1)) iv1
          v (@initial_arrow_family_action_target_path B C t T0 (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
          (@cokernel_adjunction_func C S t T0 Q) D) Y v))
        (@eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
          (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (@Transf B C
          (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (λ z : τ (@Transf B C
          (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
          WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)), (@comp_fapp0 (Functor_cat B C)
          (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
          WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v z)) u1 (@fapp0 _ _
          (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func
          WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 Q))
          (@cokernel_adjunction_projection C S t T0 Q)) (@one_cat_cokernel_family_unit_target_path B C S C1 t T0
          Q D))));

// Use the existing graph presentation of the same original quotient.
symbol one_cat_cokernel_family_projection_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C)) (v : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t
    T0 Q) D) Y))
  : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@sym_transf_tapp0_transf
    B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
    Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t
    T0)) Y)) (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) v) walking_arrow_tgt)
    (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0
    B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v
    (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)))
≔ (@eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)
  (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0
  (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y)) (@one_cat_adjunction_family_transpose_func B
  (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C
  S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) v) walking_arrow_tgt)
  (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 Q)) (@cokernel_adjunction_projection C S t T0 Q)))
  (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q D))
  (@one_cat_cokernel_family_projection_raw_path B C S C1 t T0 Q D Y v) (@eq_ap (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) C (@cokernel_adjunction_func C S t T0 Q) D)) (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) Y) (λ z : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)), (@comp_fapp0
  (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v z)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@cokernel_adjunction_func C S t T0 Q)) (@cokernel_adjunction_projection C S t T0 Q))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) (@eq_sym (@Transf B C (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D)) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 Q)) (@cokernel_adjunction_projection C S t
  T0 Q)) (@one_cat_cokernel_family_projection_whisker_path B C S C1 t T0 Q D))));

// The first-class native observer computes that same ambient composite.
symbol one_cat_cokernel_family_projection_functor_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C)) (v : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t
    T0 Q) D) Y))
  : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@fapp0 (Hom_cat
    (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B C)
    (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
    WalkingArrow_cat C walking_arrow_tgt) D) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
    C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) (@fapp0 (Functor_cat B C) (Functor_cat
    B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0)) Y))) (@one_cat_cokernel_family_projection_func B C S C1 t T0 Q D Y) v)
    (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0
    B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v
    (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)))
≔ (@eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@fapp0 (Hom_cat
  (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B C) (@fapp0
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
  WalkingArrow_cat C walking_arrow_tgt) D) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0)) Y))) (@one_cat_cokernel_family_projection_func B C S C1 t T0 Q D Y) v)
  (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0
  (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y)) (@one_cat_adjunction_family_transpose_func B
  (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C
  S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) v) walking_arrow_tgt)
  (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q D))
  (@one_cat_cokernel_family_projection_beta B C S C1 t T0 Q D Y v)
  (@one_cat_cokernel_family_projection_path B C S C1 t T0 Q D Y v));
