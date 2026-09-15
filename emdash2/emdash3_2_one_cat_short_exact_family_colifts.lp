/* Whole short-exact row colifts through original Q and the existing row inverse. */
require open emdash.emdash3_2_one_cat_short_exact_family_cancellation;
require open emdash.emdash3_2_one_cat_cokernel_family_reconstruction;
require open emdash.emdash3_2_cokernel_adjunction_families;

// The original row cokernel inverse reconstructs its original quotient: γ⁻¹∘p=π_i.
symbol one_cat_short_exact_cokernel_inverse_outgoing_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (R : τ (@OneCatShortExactFamily K C S C1 t T T0 P Q A D h))
  : τ (@= (@Transf K C (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func K C S t T0 Q (@zero_arrow_family_incoming_func K C t T A D h)))
  (@comp_fapp0 (Functor_cat K C) (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func K C S t
  T0 Q (@zero_arrow_family_incoming_func K C t T A D h)) (@one_cat_short_exact_family_cokernel_inverse K C S
  C1 t T T0 P Q A D h R) (@diagram_family_transf K WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q
  (@zero_arrow_family_incoming_func K C t T A D h)))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt)) (@Transf K C (@diagram_family_at_func K
  WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func K C S t T0 Q
  (@zero_arrow_family_incoming_func K C t T A D h))) (λ v : τ (@Transf K C (@diagram_family_at_func K
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt)),
  (@comp_fapp0 (Functor_cat K C) (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func K C S t
  T0 Q (@zero_arrow_family_incoming_func K C t T A D h)) (@one_cat_short_exact_family_cokernel_inverse K C S
  C1 t T T0 P Q A D h R) v)) _ _ (@eq_sym _ _ _ (@one_cat_row_cokernel_ambient_reconstruction_path K C S C1 t
  T T0 Q A D h))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@diagram_family_at_func K
  WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func K C S t T0 Q
  (@zero_arrow_family_incoming_func K C t T A D h)) (@diagram_family_at_func K WalkingArrow_cat C D
  walking_arrow_tgt) (@cokernel_adjunction_family_func K C S t T0 Q (@zero_arrow_family_incoming_func K C t T
  A D h)) (@one_cat_short_exact_family_cokernel_inverse K C S C1 t T T0 P Q A D h R)
  (@one_cat_row_cokernel_comparison K C S C1 t T T0 Q A D h) (@cokernel_adjunction_family_projection_transf K
  C S t T0 Q (@zero_arrow_family_incoming_func K C t T A D h))) (@eq_ap (@Transf K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@zero_arrow_family_incoming_func K C t T A D h))
  (@cokernel_adjunction_family_func K C S t T0 Q (@zero_arrow_family_incoming_func K C t T A D h))) (@Transf K
  C (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func K C S
  t T0 Q (@zero_arrow_family_incoming_func K C t T A D h))) (λ v : τ (@Transf K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@zero_arrow_family_incoming_func K C t T A D h))
  (@cokernel_adjunction_family_func K C S t T0 Q (@zero_arrow_family_incoming_func K C t T A D h))),
  (@comp_fapp0 (Functor_cat K C) (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func K C S t T0 Q (@zero_arrow_family_incoming_func K C t T A D h))
  (@cokernel_adjunction_family_func K C S t T0 Q (@zero_arrow_family_incoming_func K C t T A D h)) v
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@zero_arrow_family_incoming_func K C t T A D
  h)))) _ _ (@omega_equiv_along_left_law (Functor_cat K C) (@cokernel_adjunction_family_func K C S t T0 Q
  (@zero_arrow_family_incoming_func K C t T A D h)) (@diagram_family_at_func K WalkingArrow_cat C D
  walking_arrow_tgt) (@one_cat_row_cokernel_comparison K C S C1 t T T0 Q A D h)
  (@one_cat_short_exact_family_cokernel_equiv K C S C1 t T T0 P Q A D h R)))));

// Apply the original Q descent after the same row cokernel inverse.
symbol one_cat_short_exact_family_colift [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (R : τ (@OneCatShortExactFamily K C S C1 t T T0 P Q A D h))
  (Y : τ (Functor K C)) (u : τ (@Transf K C (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
  Y))
  (z : τ (@= (@Transf K C A Y) (@comp_fapp0 (Functor_cat K C) A (@diagram_family_at_func K WalkingArrow_cat C
  D walking_arrow_src) Y u (@zero_arrow_family_incoming_transf K C t T A D h)) (@zero_arrow_family_zero_transf
  K C t T T0 A Y)))
  : τ (@Transf K C (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt) Y)
≔ (@comp_fapp0 (Functor_cat K C) (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt)
  (@cokernel_adjunction_family_func K C S t T0 Q (@zero_arrow_family_incoming_func K C t T A D h)) Y
  (@one_cat_cokernel_family_descent K C S C1 t T T0 Q (@zero_arrow_family_incoming_func K C t T A D h) Y u z)
  (@one_cat_short_exact_family_cokernel_inverse K C S C1 t T T0 P Q A D h R));

// The whole row colift reconstructs the original u after the original outgoing p.
symbol one_cat_short_exact_family_colift_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (R : τ (@OneCatShortExactFamily K C S C1 t T T0 P Q A D h))
  (Y : τ (Functor K C)) (u : τ (@Transf K C (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
  Y))
  (z : τ (@= (@Transf K C A Y) (@comp_fapp0 (Functor_cat K C) A (@diagram_family_at_func K WalkingArrow_cat C
  D walking_arrow_src) Y u (@zero_arrow_family_incoming_transf K C t T A D h)) (@zero_arrow_family_zero_transf
  K C t T T0 A Y)))
  : τ (@= (@Transf K C (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) Y) (@comp_fapp0
  (Functor_cat K C) (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt) Y (@one_cat_short_exact_family_colift K C
  S C1 t T T0 P Q A D h R Y u z) (@diagram_family_transf K WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)) u)
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@diagram_family_at_func K WalkingArrow_cat
  C
  D walking_arrow_src) (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt)
  (@cokernel_adjunction_family_func K C S t T0 Q (@zero_arrow_family_incoming_func K C t T A D h)) Y
  (@one_cat_cokernel_family_descent K C S C1 t T T0 Q (@zero_arrow_family_incoming_func K C t T A D h) Y u z)
  (@one_cat_short_exact_family_cokernel_inverse K C S C1 t T T0 P Q A D h R) (@diagram_family_transf K
  WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func K C S t T0 Q (@zero_arrow_family_incoming_func K C t T A D h))) (@Transf K
  C (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) Y) (λ v : τ (@Transf K C
  (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func K C S t
  T0 Q (@zero_arrow_family_incoming_func K C t T A D h))), (@comp_fapp0 (Functor_cat K C)
  (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func K C S t
  T0 Q (@zero_arrow_family_incoming_func K C t T A D h)) Y (@one_cat_cokernel_family_descent K C S C1 t T T0 Q
  (@zero_arrow_family_incoming_func K C t T A D h) Y u z) v)) _ _
  (@one_cat_short_exact_cokernel_inverse_outgoing_path K C S C1 t T T0 P Q A D h R))
  (@one_cat_cokernel_family_descent_ambient_reconstruction K C S C1 t T T0 Q (@zero_arrow_family_incoming_func
  K C t T A D h) Y u z)));
