/* Derive θ∘κ_ρ=0 through the original image and kernel mates. */
require open emdash.emdash3_2_one_cat_native_snake_image;

// The original ρ square and κ_ρ annihilation make jκ_ρ a K(π_a)-input.
symbol one_cat_native_snake_kernel_image_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K
    C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) B (@cokernel_adjunction_family_func
    K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) (@native_snake_quotient_transf K C S t
    T T0 Q A B X D b c h) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) B (@one_cat_native_snake_cover_first
    K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_inclusion_transf K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))))
    (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))
    (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) B (@cokernel_adjunction_family_func K C
  S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) (@native_snake_quotient_transf K C S t T T0 Q
  A B X D b c h) (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C S
  t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))) (@Transf K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c
  h) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D
  b c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))) (λ v :
  τ (@Transf K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) v
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))))) _ _ (@eq_sym _ _ _ (@one_cat_native_snake_cover_reconstruction K C S C1
  t T T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q
  A B X D b c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b
  c h) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h))) (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C S t T0 Q
  (@native_snake_incoming_diagram K C t T A B X D b c h))) (λ v : τ (@Transf K C (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b
  c h) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h))), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K
  C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
  t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
  (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S
  t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@cokernel_adjunction_family_func
  K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q
  A B X D b c h)) v)) _ _ (@one_cat_kernel_family_annihilation_path K C S C1 t T T0 P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))))
  (@one_cat_zero_family_postcompose_path K C C1 t T T0 (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K
  C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q
  A B X D b c h)))))));

// Lift jκ_ρ into the same image kernel on the original Q-arrow family.
symbol one_cat_native_snake_kernel_image_lift [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K
    C S C1 t T T0 P Q A B X D b c h))
≔ (@one_cat_kernel_family_lift K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@native_snake_incoming_diagram K C t T A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) B
  (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h)))) (@one_cat_native_snake_kernel_image_zero K C S C1 t T T0 P Q A B X D b c
  h));

// The original image inclusion recovers jκ_ρ.
symbol one_cat_native_snake_kernel_image_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) B) (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K
    C S C1 t T T0 P Q A B X D b c h) B (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_cover_source
    K C S C1 t T T0 P Q A B X D b c h) B (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@native_snake_incoming_diagram K C t T A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) B
  (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h)))) (@one_cat_native_snake_kernel_image_zero K C S C1 t T T0 P Q A B X D b c
  h));

// Native kernel cancellation identifies ℓκ_ρ with v followed by the image lift.
symbol one_cat_native_snake_covered_kernel_factor_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C
    S t T P (@transf_arrow_diagram_func K C X D c))) (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_cover_source
    K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K
    C X D c)) (@one_cat_native_snake_covered_lift K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))) (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K
    C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h)))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@transf_arrow_diagram_func K C X
  D c) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K
  C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
  t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
  (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_cover_source K
  C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X
  D c)) (@one_cat_native_snake_covered_lift K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h)))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func
  K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) X
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_covered_lift K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) X) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) X) (λ v : τ (@Transf K C (@one_cat_native_snake_cover_source K C S C1 t T
  T0 P Q A B X D b c h) X), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) X v
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))))) _ _ (@one_cat_native_snake_covered_lift_reconstruction K C S C1 t T T0
  P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) B
  X b (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b
  c h) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) B) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) X) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) B), (@comp_fapp0 (Functor_cat K
  C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) B X b v)) _ _ (@eq_sym _ _ _
  (@one_cat_native_snake_kernel_image_reconstruction K C S C1 t T T0 P Q A B X D b c h))) (@eq_trans _ _ _ _
  (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) B X
  b (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) X) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) X) (λ v : τ (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T
  T0 P Q A B X D b c h) X), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func
  K C S C1 t T T0 P Q A B X D b c h) X v (@one_cat_native_snake_kernel_image_lift K C S C1 t T T0 P Q A B X D b
  c h))) _ _ (@eq_sym _ _ _ (@one_cat_native_snake_image_lift_reconstruction K C S C1 t T T0 P Q A B X D b c
  h))) (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func
  K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  X D c)) X (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_kernel_image_lift
  K C S C1 t T T0 P Q A B X D b c h))))))))));

// The required θκ_ρ=0 is derived from original image cancellation and both kernel reconstructions.
symbol one_cat_native_snake_theta_kernel_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K
    C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))) (@comp_fapp0 (Functor_cat
    K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_cover_source
    K C S C1 t T T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C S t T0 Q
    (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@one_cat_native_snake_covered_transf
    K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_inclusion_transf K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))))
    (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
    D b c h))))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T
  T0 P A B X D b c h)) (@one_cat_native_snake_covered_lift K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b
  c h) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K
  C X D c))), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T
  T0 P A B X D b c h)) v)) _ _ (@one_cat_native_snake_covered_kernel_factor_path K C S C1 t T T0 P Q A B X D b c
  h)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func
  K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  X D c)) (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P
  A B X D b c h)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@one_cat_native_snake_image_lift K C S
  C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D
  b c h))) (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))) (λ v : τ (@Transf K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C S t
  T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf
  K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D
  b c h)) v (@one_cat_native_snake_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h))) _ _
  (@one_cat_native_snake_image_quotient_zero K C S C1 t T T0 P Q N A B X D b c h))
  (@one_cat_zero_family_precompose_path K C C1 t T T0 (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func
  K C S C1 t T T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))
  (@one_cat_native_snake_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h))))));
