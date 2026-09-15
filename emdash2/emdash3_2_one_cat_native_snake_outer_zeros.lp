/* Outer zero equations for the original whole six-term snake maps. */
require open emdash.emdash3_2_one_cat_native_snake_six_term_maps;

// The first two K maps compose to zero by original quotient annihilation and native K cancellation.
symbol one_cat_native_snake_kernel_pair_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1
    t T T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K
    C S C1 t T T0 Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S
    t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second
    K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_kernel_first K C S C1 t T T0 P Q A B X D b c h))
    (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
    (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@one_cat_native_snake_gamma_diagram K
  C S C1 t T T0 Q A B X D b c h) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_kernel_first K C S C1 t T T0 P Q A B X D b c h))
  (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))) (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t
  T T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q
  A B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_kernel_first K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K
  C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t T T0
  P A B X D b c h)) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X
  D b c h))) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C S t T0 Q
  (@native_snake_incoming_diagram K C t T A B X D b c h)) v (@one_cat_native_snake_kernel_first K C S C1 t T T0
  P Q A B X D b c h))) _ _ (@one_cat_native_snake_kernel_second_reconstruction K C S C1 t T T0 P Q A B X D b c
  h)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T
  P (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S
  t T P (@transf_arrow_diagram_func K C B X b)) B (@cokernel_adjunction_family_func K C S t T0 Q
  (@native_snake_incoming_diagram K C t T A B X D b c h)) (@cokernel_adjunction_family_projection_transf K C S t
  T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C S
  t T P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C S C1 t T T0 P Q A B X D
  b c h))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) B) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c
  h)) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))) (λ
  v : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t
  T T0 P A B X D b c h)) B), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) B (@cokernel_adjunction_family_func K C
  S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b
  c h)) v)) _ _ (@one_cat_native_snake_kernel_first_reconstruction K C S C1 t T T0 P Q A B X D b c h))
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) A B (@cokernel_adjunction_family_func K
  C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b
  c h)) (@native_snake_incoming K C t T A B X D b c h) (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K
  C A (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t T T0
  P A B X D b c h)) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X
  D b c h))) (λ v : τ (@Transf K C A (@cokernel_adjunction_family_func K C S t T0 Q
  (@native_snake_incoming_diagram K C t T A B X D b c h))), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c
  h)) A (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) v
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P
  A B X D b c h)))) _ _ (@one_cat_cokernel_family_annihilation_path K C S C1 t T T0 Q
  (@native_snake_incoming_diagram K C t T A B X D b c h))) (@eq_trans _ _ _ _
  (@one_cat_zero_family_precompose_path K C C1 t T T0 (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) A (@cokernel_adjunction_family_func K C
  S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K
  C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))) (@eq_sym _ _ _
  (@one_cat_zero_family_postcompose_path K C C1 t T T0 (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K
  C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) (@kernel_adjunction_family_inclusion_transf
  K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))))))))))));

// The last two Q maps compose to zero by original kernel annihilation and native Q cancellation.
symbol one_cat_native_snake_cokernel_pair_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S
    C1 t T T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C S t T0 Q
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
    D b c h)) (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
    D b c h)) (@one_cat_native_snake_cokernel_second K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_cokernel_first K C S C1 t T T0 P Q A B X D b c h)) (@zero_arrow_family_zero_transf K
    C t T T0 (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0
    P A B X D b c h)) (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S
    C1 t T T0 Q A B X D b c h))))
≔ (@one_cat_cokernel_family_quotient_reflect_path K C S C1 t T T0 Q (@one_cat_native_snake_alpha_diagram K C S
  C1 t T T0 P A B X D b c h) (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram
  K C S C1 t T T0 Q A B X D b c h)) (@comp_fapp0 (Functor_cat K C) (@cokernel_adjunction_family_func K C S t T0
  Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  S t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second
  K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_cokernel_first K C S C1 t T T0 P Q A B X D b c h))
  (@zero_arrow_family_zero_transf K C t T T0 (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C S
  t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_sym _ _
  _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X
  D c)) (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A
  B X D b c h)) (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D
  b c h)) (@one_cat_native_snake_cokernel_second K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_cokernel_first K C S C1 t T T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T
  T0 P A B X D b c h)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C S t T0 Q
  (@transf_arrow_diagram_func K C B X b))) (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C B X b))), (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D
  b c h)) (@one_cat_native_snake_cokernel_second K C S C1 t T T0 P Q A B X D b c h) v)) _ _
  (@one_cat_native_snake_cokernel_first_reconstruction K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _
  (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D
  c)) X (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D
  b c h)) (@one_cat_native_snake_cokernel_second K C S C1 t T T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C X D c))) (@eq_trans _
  _ _ _ (@eq_ap (@Transf K C X (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D
  b c h))) (λ v : τ (@Transf K C X (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) X
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D
  b c h)) v (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C X D c)))) _
  _ (@one_cat_native_snake_cokernel_second_reconstruction K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C X D c)) X D (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T
  T0 Q A B X D b c h)) c (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  X D c)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C X D c)) D) (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) D), (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) D
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D
  b c h)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S
  C1 t T T0 Q A B X D b c h)) v)) _ _ (@one_cat_kernel_family_annihilation_path K C S C1 t T T0 P
  (@transf_arrow_diagram_func K C X D c))) (@eq_trans _ _ _ _ (@one_cat_zero_family_postcompose_path K C C1 t T
  T0 (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) D
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D
  b c h)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S
  C1 t T T0 Q A B X D b c h))) (@eq_sym _ _ _ (@one_cat_zero_family_precompose_path K C C1 t T T0
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D
  b c h)) (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q
  A B X D b c h)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))))))))))));
