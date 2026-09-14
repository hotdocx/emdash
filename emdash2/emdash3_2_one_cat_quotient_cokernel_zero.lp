/* The actual cokernel of an original quotient has zero projection. */
require open emdash.emdash3_2_one_cat_cokernel_family_annihilation;
require open emdash.emdash3_2_one_cat_cokernel_family_reconstruction;
require open emdash.emdash3_2_one_cat_kernel_pullback_lifts;
require open emdash.emdash3_2_cokernel_adjunction_families;

// The original quotient cancels to prove that its own original cokernel projection is zero.
symbol one_cat_quotient_cokernel_zero [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ
  (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 : τ (@= (@Transf B C (@cokernel_adjunction_family_func B C S t T0 Q D) (@cokernel_adjunction_family_func B C S t
  T0 Q (@transf_arrow_diagram_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@cokernel_adjunction_family_func B C S t T0 Q D) (@cokernel_adjunction_family_projection_transf B C S t T0 Q
  D)))) (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@transf_arrow_diagram_func B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0
  Q D) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D))) (@zero_arrow_family_zero_transf B C t T T0
  (@cokernel_adjunction_family_func B C S t T0 Q D) (@cokernel_adjunction_family_func B C S t T0 Q
  (@transf_arrow_diagram_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@cokernel_adjunction_family_func B C S t T0 Q D) (@cokernel_adjunction_family_projection_transf B C S t T0 Q
  D)))))
≔ @one_cat_cokernel_family_quotient_reflect_path B C S C1 t T T0 Q D (@cokernel_adjunction_family_func B C S t T0
  Q (@transf_arrow_diagram_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@cokernel_adjunction_family_func B C S t T0 Q D) (@cokernel_adjunction_family_projection_transf B C S t T0 Q
  D))) (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@transf_arrow_diagram_func B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0
  Q D) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D))) (@zero_arrow_family_zero_transf B C t T T0
  (@cokernel_adjunction_family_func B C S t T0 Q D) (@cokernel_adjunction_family_func B C S t T0 Q
  (@transf_arrow_diagram_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@cokernel_adjunction_family_func B C S t T0 Q D) (@cokernel_adjunction_family_projection_transf B C S t T0 Q
  D)))) (@eq_trans _ _ _ _ (@one_cat_cokernel_family_annihilation_path B C S C1 t T T0 Q
  (@transf_arrow_diagram_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@cokernel_adjunction_family_func B C S t T0 Q D) (@cokernel_adjunction_family_projection_transf B C S t T0 Q
  D))) (@eq_sym _ _ _ (@one_cat_zero_family_precompose_path B C C1 t T T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0 Q D)
  (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0 Q D)
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q D))) (@cokernel_adjunction_family_projection_transf
  B C S t T0 Q D))));
