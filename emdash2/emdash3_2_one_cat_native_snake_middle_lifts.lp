/* The original K(b) lifts to E, with its two reconstructions and vanishing under θ. */
require open emdash.emdash3_2_one_cat_native_snake_six_term_maps;

// The original K(b) inclusion is killed by γπ_a.
symbol one_cat_native_snake_middle_cover_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) D)
    (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
    X b)) B D (@comp_fapp0 (Functor_cat K C) B (@cokernel_adjunction_family_func K C S t T0 Q
    (@native_snake_incoming_diagram K C t T A B X D b c h)) D (@one_cat_native_snake_gamma K C S C1 t T T0 Q A B
    X D b c h) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t
    T A B X D b c h))) (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B
    X b))) (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C B X b)) D))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C B D) (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B X b)) D) (λ v : τ (@Transf K C B D), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) B D v
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B X b)))) _ _
  (@one_cat_native_snake_gamma_reconstruction K C S C1 t T T0 Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_sym _ _
  _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) B X D c b (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B X
  b)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B X b)) X) (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B X b)) D) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B X b)) X), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  S t T P (@transf_arrow_diagram_func K C B X b)) X D c v)) _ _ (@one_cat_kernel_family_annihilation_path K C S
  C1 t T T0 P (@transf_arrow_diagram_func K C B X b))) (@one_cat_zero_family_postcompose_path K C C1 t T T0
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) X D c))));

// Lift K(b) into the original cover source E without choosing a section.
symbol one_cat_native_snake_middle_cover_lift [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h))
≔ (@one_cat_kernel_family_lift K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B X b)) (@precomposed_diagram_family_func K C B
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b
  c h))) (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_middle_cover_zero K C S C1 t T T0 P Q A B X D b c h));

// The original j:E⇒B recovers κ_b.
symbol one_cat_native_snake_middle_cover_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) B)
    (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
    X b)) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) B
    (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h))
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B X b)))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C B X b)) (@precomposed_diagram_family_func K C B
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b
  c h))) (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_middle_cover_zero K C S C1 t T T0 P Q A B X D b c h));

// The original ρ maps this lift to the actual second K-map.
symbol one_cat_native_snake_middle_cover_second_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c
    h) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
    D b c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X
  b)) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
  (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h) (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K
  C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) (@kernel_adjunction_family_inclusion_transf
  K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
  (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))) (λ v :
  τ (@Transf K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X
  b)) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K
  C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) v (@one_cat_native_snake_middle_cover_lift
  K C S C1 t T T0 P Q A B X D b c h))) _ _ (@one_cat_native_snake_cover_reconstruction K C S C1 t T T0 P Q A B X
  D b c h)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C
  S t T P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X
  D b c h) B (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c
  h)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X
  D b c h)) (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) B) (@Transf K
  C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))) (λ v :
  τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) B),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X
  b)) B (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b
  c h)) v)) _ _ (@one_cat_native_snake_middle_cover_reconstruction K C S C1 t T T0 P Q A B X D b c h)) (@eq_sym
  _ _ _ (@one_cat_native_snake_kernel_second_reconstruction K C S C1 t T T0 P Q A B X D b c h)))))));

// Kernel cancellation makes ℓ vanish on the original K(b) lift.
symbol one_cat_native_snake_middle_lift_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))) (@comp_fapp0
    (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_covered_lift K C S C1 t T T0 P Q A B X
    D b c h) (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h))
    (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C X D c))))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B X b)) (@transf_arrow_diagram_func K C X D c) (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_covered_lift K C S C1 t T T0 P Q A B X D b
  c h) (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h))
  (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C X D c))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C X D c)) X (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_covered_lift K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) X) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) X) (λ v : τ (@Transf K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) X), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) X v
  (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h))) _ _
  (@one_cat_native_snake_covered_lift_reconstruction K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  B X b (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) B) (@Transf K
  C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) X) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) B), (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) B X b
  v)) _ _ (@one_cat_native_snake_middle_cover_reconstruction K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _
  _ _ (@one_cat_kernel_family_annihilation_path K C S C1 t T T0 P (@transf_arrow_diagram_func K C B X b))
  (@eq_sym _ _ _ (@one_cat_zero_family_postcompose_path K C C1 t T T0 (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C X D c)) X (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C X D c))))))))));

// The same θ vanishes on that lift.
symbol one_cat_native_snake_middle_theta_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
    D b c h))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c
    h) (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B
    X D b c h)) (@one_cat_native_snake_covered_transf K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h)) (@zero_arrow_family_zero_transf
    K C t T T0 (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
    D b c h))))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D
  b c h)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S
  C1 t T T0 P A B X D b c h)) (@one_cat_native_snake_covered_lift K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D
  b c h))) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X
  b)) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))), (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D
  b c h)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S
  C1 t T T0 P A B X D b c h)) v)) _ _ (@one_cat_native_snake_middle_lift_zero K C S C1 t T T0 P Q A B X D b c
  h)) (@one_cat_zero_family_postcompose_path K C C1 t T T0 (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T
  T0 P A B X D b c h)))));
