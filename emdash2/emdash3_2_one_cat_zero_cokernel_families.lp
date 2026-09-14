require open emdash.emdash3_2_cokernel_adjunction_families;
require open emdash.emdash3_2_one_cat_cokernel_family_reconstruction;
require open emdash.emdash3_2_functor_category_unit_views;

// Descend id through the original cokernel of the actual zero differential.
symbol one_cat_zero_cokernel_retraction [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (Q
  : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@=
  (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt)) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
 : τ (@Transf B C (@cokernel_adjunction_family_func B C S t T0 Q D) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt))
≔ @one_cat_cokernel_family_descent B C S C1 t T T0 Q D (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) z;

// The original quotient reconstructs id under that same descent.
symbol one_cat_zero_cokernel_left_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (Q
  : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@=
  (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt)) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0 Q D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_zero_cokernel_retraction B C
  S C1 t T T0 Q D z) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) (@id (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))
≔ @one_cat_cokernel_family_descent_ambient_reconstruction B C S C1 t T T0 Q D (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt)) z;

// Original quotient cancellation gives the other law for the same retraction.
symbol one_cat_zero_cokernel_right_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (Q
  : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@=
  (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt)) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
 : τ (@= (@Transf B C (@cokernel_adjunction_family_func B C S t T0 Q D) (@cokernel_adjunction_family_func B C S t
  T0 Q D)) (@comp_fapp0 (Functor_cat B C) (@cokernel_adjunction_family_func B C S t T0 Q D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0
  Q D) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) (@one_cat_zero_cokernel_retraction B C
  S C1 t T T0 Q D z)) (@id (Functor_cat B C) (@cokernel_adjunction_family_func B C S t T0 Q D)))
≔ @one_cat_cokernel_family_quotient_reflect_path B C S C1 t T T0 Q D (@cokernel_adjunction_family_func B C S t T0
  Q D) (@comp_fapp0 (Functor_cat B C) (@cokernel_adjunction_family_func B C S t T0 Q D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0 Q D)
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) (@one_cat_zero_cokernel_retraction B C S C1
  t T T0 Q D z)) (@id (Functor_cat B C) (@cokernel_adjunction_family_func B C S t T0 Q D)) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@cokernel_adjunction_family_func B C S t T0 Q D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0 Q D)
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) (@one_cat_zero_cokernel_retraction B C S C1
  t T T0 Q D z) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D))) (@eq_ap (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt)) (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@cokernel_adjunction_family_func B C S t T0 Q D)) (λ h : τ (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)),
  (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0
  Q D) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) h)) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0
  Q D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_zero_cokernel_retraction
  B C S C1 t T T0 Q D z) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) (@id (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@one_cat_zero_cokernel_left_path B C
  S C1 t T T0 Q D z)));

// Fixed-forward invertibility belongs to the original cokernel projection.
symbol one_cat_zero_cokernel_omega [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ
  (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@=
  (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt)) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@cokernel_adjunction_family_func B C S t T0 Q D) (@cokernel_adjunction_family_projection_transf B C S t T0 Q
  D))
≔ @omega_equiv_along_intro (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@cokernel_adjunction_family_func B C S t T0 Q D) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)
  (@one_cat_zero_cokernel_retraction B C S C1 t T T0 Q D z) (@one_cat_zero_cokernel_retraction B C S
  C1 t T T0 Q D z) (@one_cat_zero_cokernel_left_path B C S C1 t T T0 Q D z)
  (@one_cat_zero_cokernel_right_path B C S C1 t T T0 Q D z);
