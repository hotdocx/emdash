/* Ambient quotient reconstruction/cancellation from the original native mate. */
require open emdash.emdash3_2_one_cat_cokernel_family_projection_paths;

// The actual original q_D reconstructs the whole input after descent.
symbol one_cat_cokernel_family_descent_ambient_reconstruction [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 :
  τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C)) (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)) (z : τ (@=
    (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y) (@comp_fapp0 (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) Y u (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator)) (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C
    D walking_arrow_src) Y)))
  : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@comp_fapp0 (Functor_cat
    B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y (@one_cat_cokernel_family_descent B C S C1 t T
    T0 Q D Y u z) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) u)
≔ (@eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@comp_fapp0
  (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y (@one_cat_cokernel_family_descent B C S C1 t T T0
  Q D Y u z) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) (@sym_transf_tapp0_transf B
  WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y)
  (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0))
  Y)) (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
  WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0)
  (@cokernel_adjunction_evidence C S t T0 Q) D Y) (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z))
  walking_arrow_tgt) u (@eq_sym (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)
  (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0
  (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y)) (@one_cat_adjunction_family_transpose_func B
  (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C
  S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y)
  (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z)) walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) C (@cokernel_adjunction_func C S t T0 Q) D) Y (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z)
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q D))
  (@one_cat_cokernel_family_projection_path B C S C1 t T0 Q D Y (@one_cat_cokernel_family_descent B C S C1 t T
  T0 Q D Y u z))) (@one_cat_cokernel_family_descent_reconstruction B C S C1 t T T0 Q D Y u z));

// Precomposition by the original whole quotient reflects equality.
symbol one_cat_cokernel_family_quotient_reflect_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C)) (u v : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t
    T0 Q) D) Y))
  (p : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@comp_fapp0
    (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y u
    (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) (@comp_fapp0 (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v
    (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)))) : τ (@= (@Transf B C (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y) u v)
≔ @one_cat_cokernel_family_projection_reflect_path B C S C1 t T T0 Q Y D u v
    (@eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat
      WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
      (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) D
      (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
      WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y)) (@one_cat_adjunction_family_transpose_func B
      (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1
      (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t
      T0 Q) D Y) u) walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
      D) Y u (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) (@sym_transf_tapp0_transf B
      WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
      Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
      (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat
      (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
      WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t
      T0)) Y)) (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C
      (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
      (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) v) walking_arrow_tgt)
      (@one_cat_cokernel_family_projection_path B C S C1 t T0 Q D Y u) (@eq_trans (@Transf B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@comp_fapp0 (Functor_cat B C)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
      WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y u
      (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) (@comp_fapp0 (Functor_cat B C)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
      WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v
      (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) (@sym_transf_tapp0_transf B
      WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
      Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
      (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat
      (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
      WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t
      T0)) Y)) (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C
      (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
      (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) v) walking_arrow_tgt) p
      (@eq_sym (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat
      WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
      (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) D
      (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
      WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y)) (@one_cat_adjunction_family_transpose_func B
      (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1
      (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t
      T0 Q) D Y) v) walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
      D) Y v (@cokernel_adjunction_family_projection_transf B C S t T0 Q D))
      (@one_cat_cokernel_family_projection_path B C S C1 t T0 Q D Y v))));
