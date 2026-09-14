/* Whole original quotient: native observer, reconstruction and cancellation. */
require open emdash.emdash3_2_one_cat_cokernel_family_reconstruction;

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (b : τ (Obj B))
  ⊢ (@tapp0_fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) b
    (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) ≡ (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 Q) (@fapp0
    B (Functor_cat WalkingArrow_cat C) D b) (@cokernel_adjunction_projection C S t T0 Q));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C)) (v : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t
    T0 Q) D) Y))
  ⊢ (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat
    (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) D) (@fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt)
    (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y))) (@one_cat_cokernel_family_projection_func B C S C1
    t T0 Q D Y) v) ≡ (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0)) Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0
    (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y)) (@one_cat_adjunction_family_transpose_func B
    (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func
    C S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) v)
    walking_arrow_tgt);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C)) (v : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t
    T0 Q) D) Y))
  ⊢ (@one_cat_cokernel_family_projection_functor_path B C S C1 t T0 Q D Y v) : τ (@= (@Transf B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B C) (@fapp0
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
    WalkingArrow_cat C walking_arrow_tgt) D) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
    C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) (@fapp0 (Functor_cat B C) (Functor_cat
    B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0)) Y))) (@one_cat_cokernel_family_projection_func B C S C1 t T0 Q D Y) v)
    (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0
    B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v
    (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C)) (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)) (z : τ (@=
    (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y) (@comp_fapp0 (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) Y u (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator)) (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C
    D walking_arrow_src) Y)))
  ⊢ (@one_cat_cokernel_family_descent_ambient_reconstruction B C S C1 t T T0 Q D Y u z) : τ (@= (@Transf B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@comp_fapp0 (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y (@one_cat_cokernel_family_descent B C S C1 t T
    T0 Q D Y u z) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) u);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C)) (u v : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t
    T0 Q) D) Y)) (p : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)
    (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0
    B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y u
    (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) (@comp_fapp0 (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y v (@cokernel_adjunction_family_projection_transf
    B C S t T0 Q D))))
  ⊢ (@one_cat_cokernel_family_quotient_reflect_path B C S C1 t T T0 Q D Y u v p) : τ (@= (@Transf B C (@comp_cat_fapp0
    B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y) u v);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C)) (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)) (z : τ (@=
    (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y) (@comp_fapp0 (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) Y u (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator)) (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C
    D walking_arrow_src) Y))) (z2 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) Y) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u (@diagram_family_transf
    B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)))
  ⊢ (@one_cat_cokernel_family_quotient_reflect_path B C S C1 t T T0 Q D Y (@one_cat_cokernel_family_descent B C S C1 t
    T T0 Q D Y u z) (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z2) (@eq_trans (@Transf B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@comp_fapp0 (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y (@one_cat_cokernel_family_descent B C S C1 t T
    T0 Q D Y u z) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) u (@comp_fapp0 (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y (@one_cat_cokernel_family_descent B C S C1 t T
    T0 Q D Y u z2) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D))
    (@one_cat_cokernel_family_descent_ambient_reconstruction B C S C1 t T T0 Q D Y u z) (@eq_sym (@Transf B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@comp_fapp0 (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y (@one_cat_cokernel_family_descent B C S C1 t T
    T0 Q D Y u z2) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) u
    (@one_cat_cokernel_family_descent_ambient_reconstruction B C S C1 t T T0 Q D Y u z2)))) : τ (@= (@Transf B C
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y)
    (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z) (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D
    Y u z2));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C)) (u v : τ (Obj (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q))
    D) Y)))
  ⊢ (@fapp1_func (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat
    (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) D) (@fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt)
    (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y))) (@one_cat_cokernel_family_projection_func B C S C1
    t T0 Q D Y) u v) : τ (Functor (Hom_cat (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q)) D) Y) u v) (Hom_cat (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C
    walking_arrow_tgt) D) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0)) Y))) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) D)
    (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
    WalkingArrow_cat C walking_arrow_tgt) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) Y)))
    (@one_cat_cokernel_family_projection_func B C S C1 t T0 Q D Y) u) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) Y) (Hom_cat (Functor_cat B C) (@fapp0
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
    WalkingArrow_cat C walking_arrow_tgt) D) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
    C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) (@fapp0 (Functor_cat B C) (Functor_cat
    B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0)) Y))) (@one_cat_cokernel_family_projection_func B C S C1 t T0 Q D Y) v)));

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor
    B C)) (u v : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t
    T0 Q) D) Y))
  ⊢ (@eq_refl (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0
    Q) D) Y) u) : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func
    C S t T0 Q) D) Y) u v);

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Q2 : τ
    (@CokernelAdjunctionStructure C S t T0))
  ⊢ (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) : τ (@Transf B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q2) D));
