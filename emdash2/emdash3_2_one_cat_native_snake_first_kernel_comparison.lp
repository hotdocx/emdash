/* Native comparison between K(k2) and K(v), retaining the original image/kernel choices. */
require open emdash.emdash3_2_one_cat_native_snake_comparison_kernels;

// The original κ_bκ_k2 is killed by π_a.
symbol one_cat_native_snake_first_kernel_image_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
    (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) B
    (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))
    (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D
    b c h)) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    B X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A
    B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) B
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))))
    (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    B X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A
    B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) B
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b
  c h)) (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))) (λ v :
  τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C S t T0 Q
  (@native_snake_incoming_diagram K C t T A B X D b c h)) v (@kernel_adjunction_family_inclusion_transf K C S t
  T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K
  C B X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A
  B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))))) _ _ (@eq_sym _ _ _
  (@one_cat_native_snake_kernel_second_reconstruction K C S C1 t T T0 P Q A B X D b c h))) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q
  A B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))))) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
  K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C S t T0 Q
  (@native_snake_incoming_diagram K C t T A B X D b c h))) (λ v : τ (@Transf K C (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C S
  t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C
  S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) v)) _ _
  (@one_cat_kernel_family_annihilation_path K C S C1 t T T0 P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))))
  (@one_cat_zero_family_postcompose_path K C C1 t T T0 (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q
  A B X D b c h)))))));

// Lift into the original image kernel on Arr(π_a).
symbol one_cat_native_snake_first_kernel_image_lift [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h))
≔ (@one_cat_kernel_family_lift K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@native_snake_incoming_diagram K C t T A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  B X b)) B (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))))
  (@one_cat_native_snake_first_kernel_image_zero K C S C1 t T T0 P Q A B X D b c h));

// The original image inclusion recovers κ_bκ_k2.
symbol one_cat_native_snake_first_kernel_image_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) B) (@comp_fapp0 (Functor_cat
    K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) B
    (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_first_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h)) (@comp_fapp0 (Functor_cat
    K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) B
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K
  C B X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A
  B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@native_snake_incoming_diagram K C t T A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  B X b)) B (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))))
  (@one_cat_native_snake_first_kernel_image_zero K C S C1 t T T0 P Q A B X D b c h));

// The image lift is killed by the original v:Im(a)⇒K(c).
symbol one_cat_native_snake_first_kernel_image_lift_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))) (@comp_fapp0
    (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h) (@one_cat_native_snake_first_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h))
    (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    B X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A
    B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@transf_arrow_diagram_func K C X D c) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K
  C B X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A
  B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h))
  (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))) (@eq_trans _ _ _ _
  (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) X (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) X) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) X) (λ v : τ (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0
  P Q A B X D b c h) X), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) X v
  (@one_cat_native_snake_first_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h))) _ _
  (@one_cat_native_snake_image_lift_reconstruction K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) B X b
  (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) B) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) X) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) B), (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) B X b v)) _ _
  (@one_cat_native_snake_first_kernel_image_reconstruction K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _
  _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C B X b)) B X b (@kernel_adjunction_family_inclusion_transf K C S t
  T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) X)
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) X) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) X), (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C B X b)) X v (@kernel_adjunction_family_inclusion_transf K C S t T
  P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  B X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B
  X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))))) _ _
  (@one_cat_kernel_family_annihilation_path K C S C1 t T T0 P (@transf_arrow_diagram_func K C B X b)))
  (@eq_trans _ _ _ _ (@one_cat_zero_family_precompose_path K C C1 t T T0 (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K
  C B X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A
  B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) X
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))) (@eq_sym _ _ _
  (@one_cat_zero_family_postcompose_path K C C1 t T T0 (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) X
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C X D c))))))))))));

// Native lifting gives χ:K(k2)⇒K(v).
symbol one_cat_native_snake_first_kernel_to_image_kernel [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))))
≔ (@one_cat_kernel_family_lift K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_kernel_image_lift_zero K C S C1 t T T0 P Q A B X D b c h));

// The original K(v) inclusion reconstructs the image lift.
symbol one_cat_native_snake_first_kernel_to_image_kernel_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory
  C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func
    K C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second
    K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func
    K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    S t T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X
    D b c h))) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) (@one_cat_native_snake_first_kernel_to_image_kernel K C S C1 t T T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K
  C B X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A
  B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_kernel_image_lift_zero K C S C1 t T T0 P Q A B X D b c h));

// The original image/kernel inclusion is killed by b.
symbol one_cat_native_snake_first_image_kernel_middle_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) X) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) B X b (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) B
    (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))))) (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) X))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K C S
  C1 t T T0 P Q A B X D b c h) B X b (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b
  c h) X) (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) X) (λ v : τ (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) X),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) X v
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))))) _ _ (@eq_sym _ _ _ (@one_cat_native_snake_image_lift_reconstruction K C S C1 t T T0 P Q A B X D b c
  h))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K C S
  C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D
  c)) X (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C X D c))) (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) X) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func
  K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C X D c))), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func
  K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C X D c)) X (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C X D c)) v)) _ _ (@one_cat_kernel_family_annihilation_path K C S C1 t T T0 P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)))) (@one_cat_zero_family_postcompose_path
  K C C1 t T T0 (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) X
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C X D c)))))));

// Native lifting gives K(v)⇒K(b).
symbol one_cat_native_snake_first_image_kernel_to_middle [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)))
≔ (@one_cat_kernel_family_lift K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@transf_arrow_diagram_func K C B X b)
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) B
  (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h)))) (@one_cat_native_snake_first_image_kernel_middle_zero K C S C1 t T T0 P Q A B X D b c h));

// Its original inclusion recovers κ_Imκ_v.
symbol one_cat_native_snake_first_image_kernel_middle_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory
  C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) B) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S
    t T P (@transf_arrow_diagram_func K C B X b)) B (@kernel_adjunction_family_inclusion_transf K C S t T P
    (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_first_image_kernel_to_middle K C S C1 t T T0
    P Q A B X D b c h)) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K C
    S C1 t T T0 P Q A B X D b c h) B (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h)))))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@transf_arrow_diagram_func K C B X b)
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) B
  (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h)))) (@one_cat_native_snake_first_image_kernel_middle_zero K C S C1 t T T0 P Q A B X D b c h));

// The reconstructed map is killed by the actual second K-map.
symbol one_cat_native_snake_first_image_kernel_second_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A
    B X D b c h))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S
    t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second
    K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_first_image_kernel_to_middle K C S C1 t T T0 P Q A
    B X D b c h)) (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_gamma_diagram K
  C S C1 t T T0 Q A B X D b c h) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_first_image_kernel_to_middle K C S C1 t T T0 P Q A B X
  D b c h)) (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))) (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q
  A B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_image_kernel_to_middle K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
  (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) v
  (@one_cat_native_snake_first_image_kernel_to_middle K C S C1 t T T0 P Q A B X D b c h))) _ _
  (@one_cat_native_snake_kernel_second_reconstruction K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C B X b)) B (@cokernel_adjunction_family_func K C S t T0 Q
  (@native_snake_incoming_diagram K C t T A B X D b c h)) (@cokernel_adjunction_family_projection_transf K C S t
  T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C S
  t T P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_first_image_kernel_to_middle K C S C1 t T
  T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) B) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func
  K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))) (λ v :
  τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) B), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) B (@cokernel_adjunction_family_func K C
  S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b
  c h)) v)) _ _ (@one_cat_native_snake_first_image_kernel_middle_reconstruction K C S C1 t T T0 P Q A B X D b c
  h)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K C S
  C1 t T T0 P Q A B X D b c h) B (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram
  K C t T A B X D b c h)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q
  (@native_snake_incoming_diagram K C t T A B X D b c h)) (@one_cat_native_snake_image_inclusion K C S C1 t T T0
  P Q A B X D b c h) (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b
  c h) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
  (λ v : τ (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K
  C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) v
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))))) _ _ (@one_cat_kernel_family_annihilation_path K C S C1 t T T0 P (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@native_snake_incoming_diagram K C t T A B X D b c h)))) (@eq_trans _ _ _ _
  (@one_cat_zero_family_precompose_path K C C1 t T T0 (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K C S
  C1 t T T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K
  C t T A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h)))) (@eq_sym _ _ _ (@one_cat_zero_family_postcompose_path K C C1 t T T0 (@kernel_adjunction_family_func K C
  S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t
  T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K
  C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) (@kernel_adjunction_family_inclusion_transf
  K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))))))))))));

// Native lifting gives η:K(v)⇒K(k2).
symbol one_cat_native_snake_first_image_kernel_to_kernel [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))))
≔ (@one_cat_kernel_family_lift K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_image_kernel_to_middle K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_image_kernel_second_zero K C S C1 t T T0 P Q A B X D b c h));

// The original K(k2) inclusion reconstructs the middle lift.
symbol one_cat_native_snake_first_image_kernel_kernel_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory
  C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))) (@comp_fapp0
    (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_image_kernel_to_kernel K C S C1 t T T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_image_kernel_to_middle K C S C1 t T T0 P Q A B X D b c h))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_image_kernel_to_middle K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_image_kernel_second_zero K C S C1 t T T0 P Q A B X D b c h));

// Both native reconstructions derive ηχ=id; no section is assumed.
symbol one_cat_native_snake_first_kernel_retraction_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func
    K C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second
    K C S C1 t T T0 P Q A B X D b c h)))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func
    K C B X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0
    Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_image_kernel_to_kernel K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_first_kernel_to_image_kernel K C S C1 t T T0 P Q A B X D b c h)) (@id (Functor_cat K
    C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)) (@comp_fapp0 (Functor_cat K
  C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_image_kernel_to_kernel K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_kernel_to_image_kernel K C S C1 t T T0 P Q A B X D b c h)) (@id (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h)))) (@eq_trans _ _ _ _ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_image_kernel_to_kernel K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_kernel_to_image_kernel K C S C1 t T T0 P Q A B X D b c h)) (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func
  K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C B X b))) (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func
  K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C B X b))), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) v
  (@one_cat_native_snake_first_kernel_to_image_kernel K C S C1 t T T0 P Q A B X D b c h))) _ _
  (@one_cat_native_snake_first_image_kernel_kernel_reconstruction K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_kernel_family_inclusion_reflect_path K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@transf_arrow_diagram_func K C B X b) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K
  C B X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A
  B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func
  K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_first_image_kernel_to_middle K C S
  C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_first_kernel_to_image_kernel K C S C1 t T T0 P Q A B X D b
  c h)) (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c
  h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t
  T P (@transf_arrow_diagram_func K C B X b)) B (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_first_image_kernel_to_middle K C S C1 t T T0 P
  Q A B X D b c h) (@one_cat_native_snake_first_kernel_to_image_kernel K C S C1 t T T0 P Q A B X D b c h))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) B) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) B) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) B), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h))) B v (@one_cat_native_snake_first_kernel_to_image_kernel K C S C1 t T T0 P Q A B X D b c h))) _ _
  (@one_cat_native_snake_first_image_kernel_middle_reconstruction K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans
  _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func
  K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) B (@one_cat_native_snake_image_inclusion
  K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_kernel_to_image_kernel K C S C1 t T T0 P Q A B X D b c h))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c
  h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) B) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
  D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K
  C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) B
  (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h) v)) _ _
  (@one_cat_native_snake_first_kernel_to_image_kernel_reconstruction K C S C1 t T T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_kernel_image_reconstruction K C S C1 t T T0 P Q A B X D b c h))))))));
